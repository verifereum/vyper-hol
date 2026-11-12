Theory bodyPtrPopNestedLiveContinuation
Ancestors
  bodyPtrPopNestedLiveEntry bodyPtrPopNestedLiveSuffixFrame bodyPtrPopNestedLiveSuffix
  bodyPtrPopNestedLivePositivePost exprSimPopNestedLocalProps
  gasSummaryComposePtr fragGasPathPtr bodyPtrDefs
  vyperState venomState compileEnv loweringStateRelDefs finite_map exprSimDefs venomExecSemantics fragExec
  vyperLookup vyperScopePreservation exprSimPopNestedLocalMemory exprSimProps
  appendStorageGhostPtr bodyPtrPopNestedLiveSource bodyPtrPopTargetDefs
  stmtPoppedKeys exprSimHypsDefs
  bodyPtrPopNestedLiveHandoff reasonCopySourcePtr
  exprSimPopNestedBase exprSimPopNestedLocalHandoff exprSimPopNestedLocalSuffix
  exprSimPopNestedLocalSource exprLowering exprLoweringProps stmtLoweringMono
  exprSimHypsDefs emitHelperProps vyperEvalExprPreservesScopesDom
  vyperInterpreter vyperAST vyperTypeSystem loweringPosts valueEncoding valueEncodingDefs

Theorem pop_empty_memory_marked_ptr:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV [])) /\
  gas_path_ptr D 0 ctx func PG G tn s 0 H tf r ==>
  gas_marked_exec_ptr D (ctx,func) PG (pop_place cx (MemoryPlace id path))
    (es,s,G,tn) [] (INR (Error (RuntimeError "pop empty memory array"))) es H tf r
Proof
  strip_tac >> rewrite_tac[gas_marked_exec_ptr_def] >>
  simp[] >> gen_tac >> irule pop_memory_place_live_empty >> simp[]
QED

Theorem pop_positive_memory_marked_ptr:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  gas_path_ptr D 0 ctx func PG G tn s 0 H tf r ==>
  gas_marked_exec_ptr D (ctx,func) PG (pop_place cx (MemoryPlace id path))
    (es,s,G,tn) []
    (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV &(LENGTH vs-1))]))))
    (es with scopes := pre ++ sc |+ (id,entry with
      <|value := updated;
        popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest)
    H tf r
Proof
  strip_tac >> rewrite_tac[gas_marked_exec_ptr_def] >> simp[] >>
  gen_tac >> irule pop_memory_place_live >> simp[]
QED

Theorem pop_empty_memory_continuation:
  gas_marked_exec_ptr D (ctx,func) PG (eval_target_place cx bt)
    (es,s0,G0,tn0) marks (INL (MemoryPlace id path)) mid G tn (OK s) /\
  find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV [])) /\
  compile_dynarray_pop (Var src) 32 scale ctor imm LocMemory sm = (dst,sb) /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = 0w ==>
  ?res fin H tf rr.
    gas_marked_exec_ptr D (ctx,func) PG
      (bind (eval_target_place cx bt) (pop_place cx))
      (es,s0,G0,tn0) marks res fin H tf rr /\
    exit_result rr /\ expr_exit res rr
Proof
  strip_tac >> drule_all pop_memory_suffix_empty_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`INR (Error (RuntimeError "pop empty memory array"))`,
    `mid with gas_obs := []`, `H`, `tf`,
    `Abort Revert_abort (revert_state (set_returndata [] t))`] >>
  conj_tac
  >- (irule (SRULE [listTheory.APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      goal_assum drule >>
      irule pop_empty_memory_marked_ptr >> simp[] >> metis_tac[]) >>
  simp[expr_exit_def, exit_result_def]
QED

Theorem pop_positive_memory_source:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\ mutable_place_path entry.type path /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] ==>
  ?updated scopes'.
    assign_subscripts entry.type entry.value path
      (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
    scopes' = pre ++ sc |+ (id,entry with <|value := updated;
      popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest /\
    pop_place cx (MemoryPlace id path) es =
      (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV &(LENGTH vs-1))]))),
       es with scopes := scopes') /\
    read_result cx (PlaceR (MemoryPlace id
      (path ++ [ValueSubscript (IntV &(LENGTH vs-1))]))) (es with scopes := scopes') =
      (INL (LAST vs), es with scopes := scopes') /\
    MAP FDOM es.scopes = MAP FDOM scopes' /\
    lookup_scopes id scopes' = SOME (entry with <|value := updated;
      popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) /\
    (!j. j <> id ==> lookup_scopes j scopes' = lookup_scopes j es.scopes)
Proof
  strip_tac >> drule_all pop_memory_live_transition >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  fs[LET_THM] >> conj_tac
  >- (drule pop_place_scopes_dom >> simp[]) >>
  conj_tac
  >- (irule lookup_scopes_update >>
      drule find_containing_scope_pre_none >> simp[]) >>
  drule find_containing_scope_structure >> strip_tac >>
  simp[lookup_scopes_update_other]
QED

(* A positive suffix returns its own counted endpoint, never an S1 witness. *)
Theorem pop_positive_memory_suffix:
  expr_has_effect e /\
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  stmt_state_rel ctx func cenv cx mid s /\ wb_frame cenv es mid sa s0 s /\
  ghost_inv d cenv cx mid G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_rel func cenv mid.scopes s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ popped_keys_indexed mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\ mutable_place_path entry.type path /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  val_wf entry.type entry.value /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME b /\
  local_region cenv mid.scopes s id (w2n b) sz /\ k+32 <= sz /\
  type_memory_size entry.type <= sz /\
  mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic n)) /\
  local_path_at cenv cx id k (ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  post_value_type cenv e = expr_type e /\
  compile_dynarray_pop (Var src) 32 (type_memory_size etv) ctor imm LocMemory sm = (dst,sb) /\
  fn_has_code sm sb func /\ not_fresh_at sm src /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_covers G tn src s span /\ lookup_var src s = SOME a /\
  w2n a = w2n b+k /\
  local_place_at cenv cx id (k + 32 + (LENGTH vs - 1) * type_memory_size etv) etv
    (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w (LENGTH vs) /\ LENGTH vs < dimword(:256) /\
  32+(LENGTH vs-1)*type_memory_size etv+type_memory_size etv <= span /\
  w2n a+span < dimword(:256) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_size etv ==>
  ?result fin out t H tf.
    dst = Var out /\ fin.gas_obs = mid.gas_obs /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_marked_exec_ptr D (ctx,func) PG (pop_place cx (MemoryPlace id path))
      (mid,s,G,tn) [] (INL result) fin H tf (OK t) /\
    vv_post ctx func cenv cx e es sa sb s0 fin result
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) t /\
    ghost_inv d cenv cx fin H tf t /\
    ptr_vv_ok cx (expr_type e) result
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) fin H tf t /\
    ptr_buf_ok cenv e (Var out) H t /\
    ghost_kept cenv es sa G0 tn0 s0 H tf
Proof
  strip_tac >>
  `subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n))` by
    metis_tac[mem_path_offset_sound] >>
  drule_all pop_positive_memory_source >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  drule_all pop_memory_suffix_positive_framed_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_scopes id mid.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `w2n (n2w (w2n a+32+(LENGTH vs-1)*type_memory_size etv):bytes32) =
    w2n b+k+32+(LENGTH vs-1)*type_memory_size etv` by simp[] >>
  qmatch_asmsub_abbrev_tac `read_result cx result (mid with scopes := scopes')` >>
  qexistsl_tac [`result`, `mid with scopes := scopes'`, `out`, `t`, `H`, `tf`] >>
  simp[] >> conj_tac
  >- (simp[Abbr `result`] >> irule pop_positive_memory_marked_ptr >>
      simp[] >> metis_tac[]) >>
  `vv_post ctx func cenv cx e es sa sb s0 (mid with scopes := scopes') result
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) t /\
   ghost_inv d cenv cx (mid with scopes := scopes') H tf t /\
   ptr_vv_ok cx (expr_type e) result
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory))
      (mid with scopes := scopes') H tf t /\
   ptr_buf_ok cenv e (Var out) H t /\ ghost_kept cenv mid sm G tn s H tf` by
    (qpat_assum `local_place_at _ _ _ _ _ _`
       (assume_tac o SIMP_RULE (srw_ss()) []) >>
     match_mp_tac (Q.INST
       [`w` |-> `n2w (w2n (a:bytes32)+32+(LENGTH vs-1)*type_memory_size etv):bytes32`]
       pop_positive_framed_posts) >> simp[record_pop_def]) >>
  qpat_x_assum `scopes' = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >> irule ghost_kept_suffix_compose >>
  qexistsl_tac [`G`, `sm`, `tn`] >> simp[]
QED

Theorem pop_normal_target_continuation:
  expr_body_pre cenv cx env (Pop ann bt) es /\
  target_root bt = NameTarget id /\ local_target_live cx id bt /\
  compile_get_target_ptr compile_expr cenv bt sa = ((hdr,loc,pt),sm) /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  fn_has_code sm sb func /\ ci_mono sa sm /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (eval_target_place cx bt)
    (es,s0,G0,tn0) marks (INL p) tend G tn (OK s) /\
  target_post ctx func cenv cx es sa sm s0 (tend with gas_obs := [])
    (PlaceR p) (Type (ArrayT ann (Dynamic cap))) (hdr,loc,pt) s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx (tend with gas_obs := []) G tn s /\
  target_ptr_ok cenv (PlaceR p) (hdr,loc,pt) G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?res fin H tf rr.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
      (bind (eval_target_place cx bt) (pop_place cx))
      (es,s0,G0,tn0) marks res fin H tf rr /\
    ((?result t. rr = OK t /\ res = INL result /\
      vv_post ctx func cenv cx (Pop ann bt) es sa sb s0
        (fin with gas_obs := []) result vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx (fin with gas_obs := []) H tf t /\
      ptr_vv_ok cx ann result vv (fin with gas_obs := []) H tf t /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type ann ==>
        ptr_buf_ok cenv (Pop ann bt) op H t) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Pop ann bt) ptr.ptr_operand H t) /\
      ghost_kept cenv es sa G0 tn0 s0 H tf) \/
     (exit_result rr /\ expr_exit res rr))
Proof
  strip_tac >>
  `place_readable cx (tend with gas_obs := []) (PlaceR p)` by fs[target_post_def] >>
  `!s path t entry err.
     eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
     lookup_scopes id t.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INR err ==>
     read_popped entry.type path entry.popped = NONE` by
    metis_tac[local_target_live_no_popped_fallback] >>
  drule gas_marked_exec_ptr_exec >> strip_tac >>
  `!path entry err. p = MemoryPlace id path /\
     lookup_scopes id tend.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INR err ==>
     read_popped entry.type path entry.popped = NONE` by
    (rpt strip_tac >>
     `eval_target_place cx bt
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL p,tend with gas_obs := [])` by
       (qpat_x_assum `gas_marked_exec F _ _ _ _ _ _ _` mp_tac >>
        rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >>
        disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
     gvs[] >>
     qpat_x_assum `!s path t entry err. _`
       (qspecl_then [`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                     `path`, `tend with gas_obs := []`, `entry`, `err`] mp_tac) >>
     simp[]) >>
  drule_all pop_counted_source_handoff >> strip_tac >> gvs[] >>
  `lookup_scopes id (tend with gas_obs := []).scopes = SOME entry` by simp[] >>
  drule_all memory_target_encoding_handoff >> strip_tac >>
  drule_all pop_memory_target_ptr_handoff >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
  simp[value_type_place_def, word_scale_def, elem_size_in_location_def,
       is_slot_addressed_def] >>
  Cases_on `compile_dynarray_pop (Var out) 32 (type_memory_bytes cenv ann)
    F cenv.ce_imm_alloca LocMemory sm` >> simp[] >> strip_tac >> gvs[] >>
  `tv = ArrayTV etv (Dynamic n)` by
    (drule mem_path_offset_sound >> simp[]) >> gvs[] >>
  `w2n (b+n2w k) = w2n b+k` by simp[arithmeticTheory.ADD_COMM] >>
  drule_all pop_robust_path_array_entry >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM tend.scopes` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     strip_tac >> drule eval_target_place_preserves_scopes_dom >> simp[]) >>
  drule_all pop_array_element_layout >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `popped_keys_indexed tend.scopes` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `expr_sim_inv _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     strip_tac >>
     drule stmtPoppedKeysTheory.eval_target_place_popped_keys_indexed >>
     fs[expr_sim_inv_def]) >>
  `~s.vs_halted` by
    (fs[gas_marked_exec_ptr_def] >>
     metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  Cases_on `vs = []` >- suspend "empty" >> suspend "positive"
QED

Resume pop_normal_target_continuation[empty]:
  qpat_x_assum `vs = []` SUBST_ALL_TAC >>
  `ptr_covers G tn out s 32` by
    (irule ptr_covers_mono >> goal_assum (drule_at Any) >>
     simp[type_memory_size_def]) >>
  `mload (w2n (b+n2w k)) s = 0w` by simp[] >>
  drule_all pop_empty_memory_continuation >> strip_tac >>
  qexistsl_tac [`res`, `fin`, `H`, `tf`, `rr`] >> simp[]
QED

Resume pop_normal_target_continuation[positive]:
  `well_formed_type_value (ArrayTV etv (Dynamic n))` by
    metis_tac[vyperPlaceStatePreservationTheory.subscripts_type_well_formed] >>
  `LENGTH vs <= n /\ LENGTH vs < dimword(:256)` by
    fs[val_wf_def, vyperTypingTheory.well_formed_type_value_def] >>
  `32+(LENGTH vs-1)*type_memory_size etv+type_memory_size etv <=
    type_memory_size (ArrayTV etv (Dynamic n))` by
    (`LENGTH vs-1+1 = LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
     `(LENGTH vs-1+1) * type_memory_size etv <= n * type_memory_size etv` by
       (irule arithmeticTheory.LESS_MONO_MULT >> simp[]) >>
     qpat_x_assum `_ * _ <= _ * _` mp_tac >>
     pure_rewrite_tac[type_memory_size_def, arithmeticTheory.RIGHT_ADD_DISTRIB,
       arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono, ci_mono_def] >>
  `local_ptrs_rel func cenv tend.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `local_place_at cenv cx id (k + 32 + (LENGTH vs - 1) * type_memory_size etv) etv
     (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))])))` by
    (`mem_step_offset (ArrayTV etv (Dynamic n))
        (ValueSubscript (IntV &(LENGTH vs - 1))) =
      SOME (32 + (LENGTH vs - 1) * type_memory_size etv, etv)` by
       (simp[loweringPostsTheory.mem_step_offset_def] >> Cases_on `vs` >> gvs[]) >>
     `mem_path_offset entry.type
        (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) =
      SOME (k + 32 + (LENGTH vs - 1) * type_memory_size etv, etv)` by
       (qspecl_then [`path`, `entry.type`, `k`, `ArrayTV etv (Dynamic n)`,
          `ValueSubscript (IntV &(LENGTH vs - 1))`,
          `32 + (LENGTH vs - 1) * type_memory_size etv`, `etv`]
          mp_tac exprSimPropsTheory.mem_path_offset_snoc >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
     rewrite_tac[loweringPostsTheory.local_place_at_def] >> rpt gen_tac >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     rpt BasicProvers.VAR_EQ_TAC >> conj_tac >- REFL_TAC >> metis_tac[]) >>
  qpat_assum `local_place_at _ _ _ _ _ _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?result fin out' t H tf.
     q = Var out' /\ fin.gas_obs = [] /\ t.vs_current_bb = r.cs_current_bb /\
     t.vs_inst_idx = LENGTH r.cs_current_insts /\
     gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (pop_place cx (MemoryPlace id path))
       (tend with gas_obs := [],s,G,tn) [] (INL result) fin H tf (OK t) /\
     vv_post ctx func cenv cx (Pop ann bt) es sa r s0 fin result
       (LocatedValue ann (mk_ptr (Var out') LocMemory)) t /\
     ghost_inv d cenv cx fin H tf t /\
     ptr_vv_ok cx ann result (LocatedValue ann (mk_ptr (Var out') LocMemory)) fin H tf t /\
     ptr_buf_ok cenv (Pop ann bt) (Var out') H t /\
     ghost_kept cenv es sa G0 tn0 s0 H tf` by
    (irule (SRULE [expr_type_def, loweringPostsTheory.expr_has_effect_thm]
       (Q.INST [`e` |-> `Pop ann bt`, `mid` |-> `tend with gas_obs := []`]
         pop_positive_memory_suffix)) >>
     qpat_assum `type_memory_bytes cenv ann = _`
       (fn th => qpat_x_assum `compile_dynarray_pop _ _ _ _ _ _ _ = _`
         (assume_tac o REWRITE_RULE [th])) >>
     simp[] >>
     qpat_assum `compile_dynarray_pop _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `ptr_covers G tn out s _` (irule_at Any) >>
     simp[] >>
     simp[expr_type_def, post_value_type_def, lowered_value_type_def,
          ci_mono_def, type_memory_size_def] >> qexists_tac `env` >>
     fs[ci_mono_def]) >>
  suspend "positive_bind"
QED

Resume pop_normal_target_continuation[positive_bind]:
  `fin with gas_obs := [] = fin` by
    simp[evaluation_state_component_equality] >>
  gvs[] >> qexistsl_tac [`INL result`, `fin`, `H`, `tf`, `OK t`] >>
  conj_tac
  >- (irule (SRULE [listTheory.APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      goal_assum drule >> simp[]) >>
  fs[contextTheory.mk_ptr_def]
QED
Finalise pop_normal_target_continuation
