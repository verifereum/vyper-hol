(*
 * Dynamic-array append over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAppend
Ancestors
  bodyFullTarget bodyAppendResolvedPre gasOutcomeFullCompose stmtLoweringMono
  loweringPosts supportedTypes exprSimSource gasShadowCompileStmtHelpers
  exprLoweringProps
  bodyFullAppendResolved placeStore bodyPtrDefs valueEncodingDefs
  assignTuplePtrStoreWord rawCallBufferPtr vyperPlaceWriteSoundness vyperTyping
  tuplePlaceSourceHead exprSimPrecompiles stmtSimForArrayFrame vyperScopePreservation
  appendStorageStageTransportPtr appendStorageStaticPtr fragGasCopyLoop instSeqPtrLo appendResolvedStorageRel
  vyperFiniteStoragePreservation assignTuplePtrLoadStep targetSubscriptStorage appendStorageGhostPtr
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

val _ = Parse.hide "body";

Theorem array_set_index_indexed_error[local]:
  !tv av i x vj err.
    array_index tv av i = SOME x /\ array_set_index tv av i vj = INR err ==>
    ?msg. err = TypeError msg
Proof
  rpt gen_tac >>
  simp[vyperValueOperationTheory.array_index_def,
       vyperValueOperationTheory.array_set_index_def, LET_THM] >>
  Cases_on `0 <= i` >> simp[] >>
  Cases_on `av`
  >~ [`DynArrayV l`]
  >- (simp[listTheory.oEL_THM] >> Cases_on `Num i < LENGTH l` >> simp[])
  >~ [`TupleV l`] >- simp[] >>
  Cases_on `tv` >> simp[] >>
  Cases_on `b` >> simp[] >>
  rename1 `Num i < n` >> Cases_on `Num i < n` >> simp[]
QED

Theorem aug_place_replace_read_error[local]:
  !path tv a old v err.
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace v) = INR err ==>
    ?msg. err = TypeError msg
Proof
  Induct_on `path` >- simp[assign_subscripts_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h`
  >~ [`ValueSubscript key`]
  >- (`?i av. key = IntV i /\ a = ArrayV av` by
        (Cases_on `key` >> fs[evaluate_subscripts_def] >>
         Cases_on `a` >> fs[]) >>
      gvs[] >>
      qpat_x_assum `evaluate_subscripts _ _ _ = _` mp_tac >>
      qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_subscripts_def, Once assign_subscripts_def, LET_THM] >>
      Cases_on `array_index tv av i` >> simp[] >>
      rename1 `array_index tv av i = SOME elt` >>
      qmatch_goalsub_abbrev_tac `assign_subscripts etv elt path` >>
      Cases_on `assign_subscripts etv elt path (Replace v)` >> simp[]
      >- metis_tac[array_set_index_indexed_error] >>
      Cases_on `evaluate_subscripts etv elt path` >> simp[] >>
      first_x_assum drule_all >> rpt strip_tac >> gvs[])
  >~ [`AttrSubscript id`]
  >- (`?al. a = StructV al` by (Cases_on `a` >> fs[evaluate_subscripts_def]) >>
      gvs[] >>
      qpat_x_assum `evaluate_subscripts _ _ _ = _` mp_tac >>
      qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_subscripts_def, Once assign_subscripts_def, LET_THM] >>
      Cases_on `ALOOKUP al id` >> simp[] >>
      rename1 `ALOOKUP al id = SOME fld` >>
      qmatch_goalsub_abbrev_tac `assign_subscripts ftv fld path` >>
      Cases_on `assign_subscripts ftv fld path (Replace v)` >> simp[] >>
      Cases_on `evaluate_subscripts ftv fld path` >> simp[] >>
      first_x_assum drule_all >> rpt strip_tac >> gvs[]) >>
  fs[evaluate_subscripts_def]
QED

(* The top-level storage/transient dynamic array. *)
Theorem body_append_storage_full:
  !cx nid e.
    (!s'' p t'.
       eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  cheat
QED

(* A local memory dynamic array named directly (gate SEQ-4806). *)
Theorem body_append_local_full:
  !cx id e.
    (!s'' p t'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (NameTarget id) e)
Proof
  rpt strip_tac >>
  Cases_on `supported_full_word_type (expr_type e)`
  >- (irule body_append_local_word_full >> metis_tac[]) >>
  rw[body_stmt_full_ok_def] >>
  fs[supported_stmt_def]
QED

Theorem append_nested_robust_path_assign:
  !path tv k ltv a b mem mem' v old result tm tm'.
    mem_path_offset tv path = SOME (k,ltv) /\
    value_has_type tv a /\ value_has_type ltv v /\
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace v) = INL result /\
    (!m. mem_agree_outside tm mem m ==> val_in_memory tv a b m) /\
    (!m. mem_agree_outside tm' mem' m ==> val_in_memory ltv v (b+k) m) /\
    (!q. q < b+k \/ b+k+type_memory_size ltv <= q ==>
      mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') /\
    (!q. (q < b+k \/ b+k+type_memory_size ltv <= q) /\ q IN tm' ==>
      q IN tm) ==>
    (!m. mem_agree_outside tm' mem' m ==> val_in_memory tv result b m)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qabbrev_tac `hybrid = GENLIST
    (\q. HD (mem_bytes_at q 1
      (if b+k <= q /\ q < b+k+type_memory_size ltv then mem else m)))
    (MAX (LENGTH mem) (LENGTH m))` >>
  `!q. mem_bytes_at q 1 hybrid = mem_bytes_at q 1
    (if b+k <= q /\ q < b+k+type_memory_size ltv then mem else m)` by
    (gen_tac >> irule LIST_EQ >>
     simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
     simp[valueEncodingProofsTheory.EL_mem_bytes_at, Abbr `hybrid`,
          EL_GENLIST, GSYM EL] >>
     Cases_on `b+k <= q /\ q < b+k+type_memory_size ltv` >>
     simp[] >> Cases_on `q < LENGTH mem` >>
     Cases_on `q < LENGTH m` >> simp[]) >>
  `mem_agree_outside tm mem hybrid` by
    (rw[mem_agree_outside_def] >>
     Cases_on `b+k <= i /\ i < b+k+type_memory_size ltv`
     >- simp[] >>
     `i < b+k \/ b+k+type_memory_size ltv <= i` by decide_tac >>
     `i NOTIN tm'` by metis_tac[] >>
     fs[mem_agree_outside_def] >> metis_tac[]) >>
  `val_in_memory tv a b hybrid` by metis_tac[] >>
  irule place_store_path_assign >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  qexistsl_tac [`old`, `v`] >> simp[] >>
  rpt strip_tac >>
  `~(b+k <= q /\ q < b+k+type_memory_size ltv)` by decide_tac >>
  simp[]
QED

Theorem append_nested_robust_array_project:
  mem_path_offset rt path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  value_has_type rt a /\ well_formed_type_value rt /\
  evaluate_subscripts rt a path = INL (ArrayV (DynArrayV vs)) /\
  (!m. mem_agree_outside tm mem m ==> val_in_memory rt a b m) ==>
  (!m. mem_agree_outside tm mem m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (b+k) m) /\
  (!i. b+k <= i /\ i < b+k+32 ==> i NOTIN tm)
Proof
  strip_tac >>
  `!m. mem_agree_outside tm mem m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (b+k) m` by
    (rpt strip_tac >> irule bodySimAugPlaceLoadTheory.aug_place_path_project >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `!m. mem_agree_outside tm mem m ==>
    mem_word_at (b+k) m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
     simp[val_in_memory_def]) >>
  drule representationCleanPtrTheory.robust_mem_word_at_clean >> simp[]
QED

Theorem append_nested_memory_reserved_lookup:
  compile_dynarray_append cenv bop vop 32 32 elem src_ty cap T LocMemory sm = ((),sb) /\
  run_inst_seq (emitted_insts sm sb) t = OK u ==>
  !x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t
Proof
  rpt strip_tac >>
  irule appendStorageStageTransportPtrTheory.run_inst_seq_non_output_vars >>
  qexists_tac `emitted_insts sm sb` >> simp[] >>
  qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def] >> strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  fs[loweringStateRelDefsTheory.not_fresh_at_def]
QED

Theorem append_nested_memory_cont_full[local]:
 !DF lo d ctx shadow_ctx PG func cx st0 lctx RetQ cenv env sa sm sb s0 G0 tn0
   mid t G tn id path entry rp sz rootw k tv vs v p bp vop w elem src_ty cap.
  body_inv (cx_tops cx) ctx cenv cx /\
  gas_admissible (append_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) mid /\
  expr_sim_inv cenv cx env mid /\ supported_full_word_type elem /\ 
  evaluate_type (get_tenv cx) elem = SOME tv /\
  type_memory_size tv = 32 /\ value_has_type tv v /\ abi_tuple_word tv v /\
  lookup_scopes id mid.scopes = SOME entry /\ entry.assignable /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var rp) sz) /\
  lookup_var rp t = SOME rootw /\
  mem_path_offset entry.type path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap))) /\
  compile_dynarray_append cenv (Var p) vop 32 32 elem src_ty cap T LocMemory sm = ((),sb) /\
  not_fresh_at sm p /\ (!x. vop = Var x ==> not_fresh_at sm x) /\
  lookup_var p t = SOME bp /\ eval_operand vop t = SOME w /\
  w = typed_val_to_w256 tv v /\ op_taint tn vop = {} /\
  ptr_covers G tn p t (32*(1+cap)) /\
  (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
  cap < dimword (:256) /\ w2n bp+32*(1+cap) <= t.vs_alloca_next /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct func /\ fn_has_code sm sb func /\
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sm t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (append_place cx (MemoryPlace id path) v) (mid,t,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
         op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  strip_tac >>
  `t.vs_alloca_next < dimword (:256)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def, exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `w2n bp + 32*(1+cap) <= dimword (:256)` by decide_tac >>
  drule_all appendMemoryRelTheory.append_memory_array_layout_general >>
  strip_tac >> gvs[] >>
  `mload (w2n bp) t = n2w (LENGTH vs)` by
    (qpat_assum `val_in_memory (ArrayTV _ _) _ _ _` mp_tac >>
     pure_rewrite_tac[valueEncodingDefsTheory.val_in_memory_def] >> strip_tac >>
     fs[venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def]) >>
  `LENGTH vs <= cap /\ LENGTH vs < dimword (:256)` by
    (fs[vyperTypingTheory.value_has_type_def] >> decide_tac) >>
  `w2n (mload (w2n bp) t) = LENGTH vs` by simp[] >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `!st. st.scopes = mid.scopes ==>
    place_type_value cx (MemoryPlace id path) st = (INL (ArrayTV tv (Dynamic cap)),st) /\
    read_place cx (MemoryPlace id path) st = (INL (ArrayV (DynArrayV vs)),st)` by
    (rpt strip_tac >>
     simp[place_type_value_def, read_place_def, get_scopes_def,
          lift_option_type_def, lift_option_def, bind_def, return_def,
          read_memory_path_def, lift_sum_def]) >>
  `!st. st.scopes = mid.scopes ==>
    append_place cx (MemoryPlace id path) v st =
    bind (lift_sum (append_element (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) v))
         (write_place cx (MemoryPlace id path)) st` by
    (rpt strip_tac >> simp[append_place_def, bind_def]) >>
  Cases_on `LENGTH vs < cap`
  >- suspend "success"
  >> suspend "capacity"
QED

Resume append_nested_memory_cont_full[capacity]:
  `!st. st.scopes = mid.scopes ==>
    append_place cx (MemoryPlace id path) v st =
      (INR (Error (RuntimeError "append overflow")),st)` by
    (rpt strip_tac >>
     simp[vyperValueOperationTheory.append_element_def,
          vyperValueTheory.compatible_bound_def, bind_def, lift_sum_def, raise_def] >>
     decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule appendMemoryPathTheory.append_memory_word_mem_ok >>
     qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     simp[venomStateTheory.eval_operand_def, arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  qabbrev_tac `lv = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `ov = STRING #"%" (toString (sm.cs_next_var+1))` >>
  qabbrev_tac `load = mk_inst sm.cs_next_id MLOAD [Var p] [lv]` >>
  qabbrev_tac `test = mk_inst (sm.cs_next_id+1) LT [Var lv; Lit (n2w cap)] [ov]` >>
  qabbrev_tac `assertinst = mk_inst (sm.cs_next_id+2) ASSERT [Var ov] []` >>
  `?rest. emitted_insts sm sb = load::test::assertinst::rest` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[NoAsms, compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
          contextTheory.compile_ptr_store_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     disch_then (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) [exprLoweringPropsTheory.emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[Abbr `load`, Abbr `test`, Abbr `assertinst`, Abbr `lv`, Abbr `ov`]) >>
  `p <> lv /\ p <> ov /\ lv <> ov` by
    (gvs[Abbr `lv`, Abbr `ov`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[emitHelperPropsTheory.fresh_var_neq, DECIDE ``n <= n+1``]) >>
  qabbrev_tac `s1 = update_var lv (mload (w2n bp) t) t` >>
  qabbrev_tac `s2 = update_var ov 0w s1` >>
  `step_inst_base load t = OK s1 /\
   step_inst_base test s1 = OK s2 /\
   step_inst_base assertinst s2 = Abort Revert_abort (revert_state (set_returndata [] s2))` by
    simp[Abbr `load`, Abbr `test`, Abbr `assertinst`, Abbr `s1`, Abbr `s2`,
         venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def,
         venomExecSemanticsTheory.exec_read1_def, venomExecSemanticsTheory.exec_pure2_def,
         venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
         venomStateTheory.update_var_def, FLOOKUP_UPDATE,
         venomExecSemanticsTheory.bool_to_word_def] >>
  `allocas_from lo t` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `ptr_covers G tn p t (32*(1+cap))` by simp[arithmeticTheory.ADD_COMM] >>
  `cap < dimword (:256) /\ w2n bp+32*(1+cap) <= dimword (:256)` by decide_tac >>
  drule_all appendMemoryPtrTheory.append_memory_word_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `DF (storage_trace_horizon mid.storage_trace)`]
    strip_assume_tac) >>
  `!D k. inst_seq_ptr D lo ctx func PG G tn
    (emitted_insts sm sb) (t with vs_inst_idx := k) Gf tnf` by
    (rpt gen_tac >>
     drule_all appendMemoryPtrTheory.append_memory_word_ptr >>
     disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr (DF _) _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  `inst_mem_below_frontier load t /\ inst_dload_in_section load t /\
   inst_mem_below_frontier test s1 /\ inst_dload_in_section test s1 /\
   inst_mem_below_frontier assertinst s2 /\ inst_dload_in_section assertinst s2` by
    (qpat_assum `run_inst_seq_mem_ok _ t` mp_tac >>
     qpat_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >> simp[]) >>
  qabbrev_tac `G1 = step_prov PG G load s1` >>
  qabbrev_tac `tn1 = step_taint load t s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 test (s2 with vs_inst_idx := SUC t.vs_inst_idx)` >>
  qabbrev_tac `tn2 = step_taint test (s1 with vs_inst_idx := SUC t.vs_inst_idx)
                                (s2 with vs_inst_idx := SUC t.vs_inst_idx) tn1` >>
  `~is_terminator load.inst_opcode /\ ~is_terminator test.inst_opcode /\
   ~is_terminator assertinst.inst_opcode` by
    simp[Abbr `load`, Abbr `test`, Abbr `assertinst`,
         venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn load t /\
    ptr_inst_ok D lo 0 ctx func G1 tn1 test (s1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    ptr_inst_ok D lo 0 ctx func G2 tn2 assertinst (s2 with vs_inst_idx := t.vs_inst_idx+2) /\
    Gf = G2 /\ tnf = tn2` by
    (gen_tac >>
     qpat_assum `!D k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`D`, `t.vs_inst_idx`] mp_tac) >>
     qpat_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[fragGasSeqPtrTheory.inst_seq_ptr_def] >>
     simp[instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def,
          Abbr `G1`, Abbr `tn1`, Abbr `G2`, Abbr `tn2`, arithmeticTheory.ADD1]) >>
  drule appendMemoryPathTheory.append_memory_word_footprint >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (fs[exprLoweringPropsTheory.same_blocks_def,
        emitHelperPropsTheory.inst_extends_def,
        exprLoweringPropsTheory.emitted_insts_def] >>
     gvs[rich_listTheory.IS_PREFIX_APPEND]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb t.vs_inst_idx = SOME load /\
   get_instruction bb (SUC t.vs_inst_idx) = SOME test /\
   get_instruction bb (t.vs_inst_idx+2) = SOME assertinst` by
    (qpat_x_assum `!i. i < LENGTH _ ==> _` mp_tac >>
     simp[] >> disch_tac >>
     first_assum (qspec_then `0` mp_tac) >>
     first_assum (qspec_then `1` mp_tac) >>
     first_x_assum (qspec_then `2` mp_tac) >> simp[arithmeticTheory.ADD1]) >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (t,G,tn) [] (OK (s1 with vs_inst_idx := SUC t.vs_inst_idx),G1,tn1)` by
    (rpt gen_tac >>
     `load.inst_opcode = MLOAD` by simp[Abbr `load`, venomInstTheory.mk_inst_def] >>
     `ptr_inst_ok D lo 0 ctx func G tn load t` by metis_tac[] >>
     `lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      load.inst_opcode <> INVOKE` by simp[] >>
     drule_all fragGasSeqPtrTheory.straight_line_origin_ptr_edge >>
     simp[Abbr `G1`, Abbr `tn1`]) >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (s1 with vs_inst_idx := SUC t.vs_inst_idx,G1,tn1) []
     (OK (s2 with vs_inst_idx := t.vs_inst_idx+2),G2,tn2)` by
    (rpt gen_tac >>
     `test.inst_opcode = LT` by simp[Abbr `test`, venomInstTheory.mk_inst_def] >>
     `ptr_inst_ok D lo 0 ctx func G1 tn1 test
       (s1 with vs_inst_idx := SUC t.vs_inst_idx)` by metis_tac[] >>
     `~(s1 with vs_inst_idx := SUC t.vs_inst_idx).vs_halted /\
      lookup_block (s1 with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (s1 with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = SOME test /\
      test.inst_opcode <> INVOKE /\
      inst_mem_below_frontier test (s1 with vs_inst_idx := SUC t.vs_inst_idx) /\
      inst_dload_in_section test (s1 with vs_inst_idx := SUC t.vs_inst_idx) /\
      step_inst_base test (s1 with vs_inst_idx := SUC t.vs_inst_idx) =
        OK (s2 with vs_inst_idx := SUC t.vs_inst_idx)` by
       (simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def] >>
        qpat_assum `get_instruction bb (SUC t.vs_inst_idx) = _` mp_tac >>
        simp[Abbr `s1`, venomStateTheory.update_var_def] >> metis_tac[]) >>
     drule_all fragGasSeqPtrTheory.straight_line_origin_ptr_edge >>
     simp[Abbr `G2`, Abbr `tn2`, arithmeticTheory.ADD1]) >>
  qabbrev_tac `s3 = s2 with vs_inst_idx := t.vs_inst_idx+2` >>
  qabbrev_tac `ab = revert_state (set_returndata [] s3)` >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (s3,G2,tn2) [] (Abort Revert_abort ab,G2,tn2)` by
    (rpt gen_tac >>
     `~s3.vs_halted /\ lookup_block s3.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s3.vs_inst_idx = SOME assertinst /\
      step_inst_base assertinst s3 = Abort Revert_abort ab` by
       (simp[Abbr `s3`, Abbr `ab`, instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def] >>
        simp[Abbr `s2`, Abbr `s1`, venomStateTheory.update_var_def,
          venomStateTheory.revert_state_def, venomStateTheory.set_returndata_def] >> metis_tac[]) >>
     simp[fragGasOriginPtrTheory.gas_origin_ptr_edge_def,
          fragGasOriginTheory.gas_origin_edge_def,
          fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
     conj_tac >- (
     qexists_tac `0` >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke,
          Abbr `assertinst`, venomInstTheory.mk_inst_def,
          gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def,
          memSafeRunTheory.mem_safe_step_def, ptrSafeRunTheory.ptr_safe_step_def] >>
     simp[fragExecTheory.exit_result_def] >>
     (disj2_tac >>
       qpat_assum `inst_mem_below_frontier _ s2` mp_tac >>
       simp[Abbr `s3`, venomInstTheory.mk_inst_def,
            instMemFrontierTheory.inst_mem_below_frontier_inst_idx] >>
       metis_tac[venomInstTheory.mk_inst_def])) >>
     qexists_tac `0` >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke,
          Abbr `assertinst`, venomInstTheory.mk_inst_def,
          gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def,
          ptrSafeRunTheory.ptr_safe_step_def] >>
     simp[fragExecTheory.exit_result_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort ab,G2,tn2)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (t,G,tn) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (_,G1,tn1) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (s3,G2,tn2) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     rpt (pop_assum kall_tac) >>
     rpt strip_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s3,G2,tn2) [] (Abort Revert_abort ab,G2,tn2)` by
       (irule (cj 3 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
        simp[fragExecTheory.exit_result_def]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s1 with vs_inst_idx := SUC t.vs_inst_idx,G1,tn1) []
        (Abort Revert_abort ab,G2,tn2)` by
       (once_rewrite_tac[GSYM APPEND_NIL] >>
        irule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
        simp[] >> goal_assum (drule_at Any) >> simp[]) >>
     once_rewrite_tac[GSYM APPEND_NIL] >>
     irule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[gasOutcomeFullTheory.gas_outcome_full_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "append overflow"))`, `mid`,
                `Abort Revert_abort ab`, `G2`, `tn2`] >>
  simp[gasSummaryTheory.gas_explicit_nil, fragExecTheory.exit_result_def] >>
  simp[bodyPtrDefsTheory.stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def]

QED

Resume append_nested_memory_cont_full[success]:
  `!x. Var p = Var x \/ vop = Var x ==> not_fresh_at sm x` by (rpt strip_tac >> gvs[]) >>
  `eval_operand (Var p) t = SOME bp` by simp[venomStateTheory.eval_operand_def] >>
  `cap < dimword (:256) /\ w2n bp+32*(1+cap) <= dimword (:256)` by decide_tac >>
  drule_all appendMemoryPathTheory.append_memory_word_run_reserved >> strip_tac >>
  first_x_assum (qspec_then `LENGTH vs` mp_tac) >> simp[] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule appendMemoryPathTheory.append_memory_word_mem_ok >>
     qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     simp[venomStateTheory.eval_operand_def, arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `allocas_from lo t` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `ptr_covers G tn p t (32*(1+cap))` by simp[arithmeticTheory.ADD_COMM] >>
  drule_all appendMemoryPtrTheory.append_memory_word_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `DF (storage_trace_horizon mid.storage_trace)`]
    strip_assume_tac) >>
  `!D k. inst_seq_ptr D lo ctx func PG G tn
    (emitted_insts sm sb) (t with vs_inst_idx := k) Gf tnf` by
    (rpt gen_tac >>
     drule_all appendMemoryPtrTheory.append_memory_word_ptr >>
     disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr (DF _) _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  drule appendMemoryPathTheory.append_memory_word_footprint >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (fs[exprLoweringPropsTheory.same_blocks_def,
        emitHelperPropsTheory.inst_extends_def,
        exprLoweringPropsTheory.emitted_insts_def] >>
     gvs[rich_listTheory.IS_PREFIX_APPEND]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[venomInstTheory.is_terminator_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (rpt gen_tac >>
     `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tnf` by
       (qpat_assum `!D k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
          (qspecl_then [`D`, `t.vs_inst_idx`] mp_tac) >>
        simp_tac (srw_ss()) []) >>
     `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     `isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
       (qpat_assum `fn_has_code sm sb func` mp_tac >>
        pure_rewrite_tac[fragExecTheory.fn_has_code_def] >> strip_tac >>
        gvs[] >> fs[rich_listTheory.IS_PREFIX_APPEND] >>
        pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
        simp_tac (srw_ss()) []) >>
     drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >>
     `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
       (qpat_assum `EVERY (\i. MEM i.inst_opcode _) _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
        first_x_assum drule >> strip_tac >> gvs[]) >>
     simp[]) >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.state_well_typed_def] >>
     metis_tac[bodySimAugPlaceLoadTheory.aug_place_lookup_typed]) >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n rootw) mem` by
    (fs[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  `w2n rootw + sz <= t.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.local_ptrs_rel_def] >> strip_tac >>
     qpat_x_assum `!name en p sz. _ ==> ?w. _`
       (qspecl_then [`id`, `entry`, `rp`, `sz`] mp_tac) >> simp[] >>
     strip_tac >> gvs[]) >>
  `w2n bp = w2n rootw+k` by
    (qpat_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[loweringPostsTheory.place_ptr_rel_def] >> strip_tac >>
     `tv0 = entry.type` by
       metis_tac[bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees,
                 optionTheory.SOME_11] >> gvs[] >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule exprSimPropsTheory.buffer_offset_no_wrap >>
     qexists_tac `sz` >> decide_tac) >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
     val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
       (w2n bp) mem` by
    (rpt strip_tac >> asm_rewrite_tac[] >>
     irule bodySimAugPlaceLoadTheory.aug_place_path_project >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  qabbrev_tac `slot = w2n bp+32*(1+LENGTH vs)` >>
  qabbrev_tac `stored = mstore slot (typed_val_to_w256 tv v) t` >>
  qabbrev_tac `out = mstore (w2n bp) (n2w (LENGTH vs+1)) stored` >>
  `u.vs_memory = out.vs_memory` by simp[Abbr `out`, Abbr `stored`, Abbr `slot`] >>
  `!mem. mem_agree_outside
      (tn.t_mem DIFF {i | slot <= i /\ i < slot+32}) stored.vs_memory mem ==>
      val_in_memory tv v slot mem` by
    (simp[Abbr `stored`] >> rpt strip_tac >>
     irule assignTuplePtrStoreWordTheory.typed_word_store_robust_ptr >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`get_tenv cx`, `elem`] >>
         simp[] >>
         fs[supportedTypesTheory.supported_full_word_type_def,
            compileEnvTheory.is_word_type_def]) >>
     qexistsl_tac [`tn.t_mem`, `t`] >> simp[]) >>
  `val_wf tv v /\ val_footprint tv v <= 32` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf,
              exprSimPropsTheory.val_footprint_le] >>
  `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory tv v slot mem` by
    (simp[Abbr `out`] >> rpt strip_tac >>
     irule rawCallBufferPtrTheory.robust_mstore_disjoint >>
     conj_tac >- simp[] >>
     qexistsl_tac [`w2n bp`,
       `tn.t_mem DIFF {i | slot <= i /\ i < slot+32}`,
       `stored`, `n2w (LENGTH vs+1)`] >>
     conj_tac >- asm_rewrite_tac[] >>
     conj_tac >- (simp[Abbr `slot`] >> decide_tac) >>
     simp[Abbr `slot`]) >>
  `tnf.t_mem = (tn.t_mem DIFF {i | slot <= i /\ i < slot+32})
       DIFF {i | w2n bp <= i /\ i < w2n bp+32}` by
    simp[Abbr `slot`] >>
  `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (vs ++ [v]))) (w2n bp) mem` by
    (rpt strip_tac >>
     irule bodyFullAppendResolvedTheory.append_local_word_robust_array >>
     conj_tac
     >- (rpt strip_tac >>
         `value_has_type tv (EL j vs)` by
           fs[vyperTypingTheory.value_has_type_def,
              vyperTypingTheory.all_have_type_EVERY, EVERY_EL] >>
         metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
     conj_tac >- simp[] >>
     qexistsl_tac [`u.vs_memory`, `tnf.t_mem`, `t.vs_memory`, `tn.t_mem`] >>
     simp[GSYM markerTheory.Abbrev_def] >>
     reverse conj_tac
     >- (conj_tac
         >- simp[Abbr `out`, Abbr `stored`, Abbr `slot`,
                 valueEncodingPropsTheory.mem_word_at_eq_mload,
                 venomMemPropsTheory.mload_mstore_same] >>
         simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
         metis_tac[]) >>
     rpt strip_tac >>
     simp[Abbr `out`, Abbr `stored`] >>
     dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     simp[Abbr `slot`] >> decide_tac) >>
  drule vyperLookupTheory.lookup_scopes_find_containing_scope >> strip_tac >>
  `?updated. assign_subscripts entry.type entry.value path
       (Replace (ArrayV (DynArrayV (vs ++ [v])))) = INL updated` by
    (Cases_on `assign_subscripts entry.type entry.value path
       (Replace (ArrayV (DynArrayV (vs ++ [v]))))` >- metis_tac[] >>
     drule_all aug_place_replace_read_error >>
     strip_tac >>
     qpat_x_assum `_ = TypeError _` (fn th =>
       qpat_x_assum `assign_subscripts _ _ _ _ = INR _`
         (assume_tac o REWRITE_RULE [th])) >>
     `append_place cx (MemoryPlace id path) v (mid with gas_obs := []) =
        (INR (Error (TypeError msg)),mid with gas_obs := [])` by
       (qpat_assum `!st. st.scopes = mid.scopes ==> append_place _ _ _ _ = _`
          (qspec_then `mid with gas_obs := []` mp_tac) >>
        simp[vyperValueOperationTheory.append_element_def, compatible_bound_def,
             vyperTypingTheory.safe_cast_well_typed, SNOC_APPEND,
             write_place_def, bind_def, ignore_bind_def, get_scopes_def,
             lift_option_type_def, type_check_def, assert_def, lift_sum_def,
             replace_memory_entry_def, raise_def, return_def]) >>
     drule_all gasContextTheory.gas_admissible_result >>
     simp[stmtSimDefsTheory.stmt_res_ok_def]) >>
  `value_has_type (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (vs ++ [v])))` by
    (fs[vyperTypingTheory.value_has_type_def,
        vyperTypingTheory.all_have_type_EVERY, EVERY_APPEND]) >>
  `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory entry.type updated (w2n rootw) mem` by
    (rpt strip_tac >> irule append_nested_robust_path_assign >>
     goal_assum (drule_at (Pat `assign_subscripts _ _ _ _ = INL _`)) >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     qexistsl_tac [`t.vs_memory`, `u.vs_memory`,
       `ArrayV (DynArrayV vs)`, `tn.t_mem`, `tnf.t_mem`] >>
     simp[GSYM markerTheory.Abbrev_def] >>
     conj_tac
     >- (rpt strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
         qpat_assum `w2n bp = _` (fn th => rewrite_tac[GSYM th]) >>
         qpat_assum `!mem. _ ==> val_in_memory (ArrayTV _ _) (ArrayV (DynArrayV (vs ++ [v]))) _ _` irule >>
         qpat_x_assum `mem_agree_outside _ _ m` mp_tac >>
         simp[arithmeticTheory.ADD_COMM]) >>
     rpt strip_tac >> simp[Abbr `out`, Abbr `stored`] >>
     dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     fs[Abbr `slot`, valueEncodingTheory.type_memory_size_def] >>
     qpat_assum `type_memory_size tv = 32` (fn th =>
       qpat_x_assum `k + (_ + (_ * type_memory_size tv + 32)) <= q`
         (mp_tac o REWRITE_RULE [th])) >> decide_tac) >>
  rename1 `find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest)` >>
  qabbrev_tac `ff = mid with scopes :=
       pre ++ (sc |+ (id,entry with <|value := updated; popped := []|>)) :: rest` >>
  `!tail. append_place cx (MemoryPlace id path) v (mid with gas_obs := tail) =
     (INL (), ff with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!st. st.scopes = mid.scopes ==> append_place _ _ _ _ = _`
       (qspec_then `mid with gas_obs := tail` mp_tac) >>
     simp[vyperValueOperationTheory.append_element_def, compatible_bound_def,
          vyperTypingTheory.safe_cast_well_typed, SNOC_APPEND,
          write_place_def, bind_def, ignore_bind_def, get_scopes_def,
          lift_option_type_def, type_check_def, assert_def, lift_sum_def,
          replace_memory_entry_def, raise_def, return_def, set_scopes_def, Abbr `ff`]) >>
  `write_place cx (MemoryPlace id path) (ArrayV (DynArrayV (vs ++ [v]))) mid =
     (INL (), ff)` by
    simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
         lift_option_type_def, type_check_def, assert_def, lift_sum_def,
         replace_memory_entry_def, return_def, set_scopes_def, Abbr `ff`] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `ff`, `INL ()`,
    `u with vs_inst_idx := LENGTH sb.cs_current_insts`, `tnf`] >>
  conj_tac >- simp[] >>
  simp[GSYM markerTheory.Abbrev_def] >> rpt strip_tac >>
  all_tac >~ [`stmt_lands _ _ _ _`]
  >- simp[loweringPostsTheory.stmt_lands_def] >>
  all_tac >~ [`cenv_top_ext _ _ _`]
  >- simp[loweringPostsTheory.cenv_top_ext_def] >>
  all_tac >~ [`stmt_state_rel _ _ _ _ _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- fs[Abbr `ff`]) >> strip_tac >>
      `stmt_state_rel H ctx func cenv cx ff out` by
        (qunabbrev_tac `out` >> qunabbrev_tac `stored` >> qunabbrev_tac `slot` >>
         irule appendMemoryRelTheory.append_memory_word_state >>
         goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
         qexistsl_tac [`cap`, `tv`, `v`] >>
         simp[] >> conj_tac
         >- (qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
             pure_rewrite_tac[loweringPostsTheory.place_ptr_rel_def] >> strip_tac >>
             `tv0 = entry.type` by
               metis_tac[bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees,
                         optionTheory.SOME_11] >>
             gvs[]) >>
         conj_tac
         >- metis_tac[bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees] >>
         irule (cj 1 stmtSimDeclStoreTheory.typed_word_store) >>
         simp[] >> qexistsl_tac [`elem`, `get_tenv cx`] >> simp[] >>
         fs[supportedTypesTheory.supported_full_word_type_def,
            compileEnvTheory.is_word_type_def]) >>
      pure_rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
      irule stmtSimAppendStorageComposeTheory.stmt_state_rel_reserved_frame >>
      goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ ff out`)) >>
      qexists_tac `sa` >> pure_asm_rewrite_tac[] >> reverse conj_tac
      >- simp[Abbr `out`, Abbr `stored`, Abbr `slot`,
              stateFrameTheory.state_frame_def,
              venomStateTheory.venom_state_component_equality] >>
      rpt strip_tac >>
      `not_fresh_at sm x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
         simp[]) >>
      fs[Abbr `out`, Abbr `stored`] >> metis_tac[]) >>
  all_tac >~ [`storage_well_formed_on _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- fs[Abbr `ff`]) >> strip_tac >>
      `storage_well_formed_on cx (ff with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx mid (FST H)` by
        (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
         simp[Abbr `ff`]) >> simp[]) >>
  all_tac >~ [`return_buf_frame _ _ _ _`]
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `t`, `sm`] >>
      simp[venomStateTheory.lookup_var_def] >>
      qpat_x_assum `!x a. not_fresh_at sm x /\ lookup_var x t = SOME a ==> lookup_var x u = SOME a` mp_tac >>
      simp[venomStateTheory.lookup_var_def]) >>
  all_tac >~ [`alloca_history _ _`]
  >- (`alloca_inv t` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
      `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
      `?rest. DROP t.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest` by
        (qpat_assum `t.vs_inst_idx = _` mp_tac >>
         qpat_assum `sb.cs_current_insts = _` mp_tac >>
         qpat_assum `sb.cs_current_bb = _` mp_tac >>
         qpat_assum `lookup_block sm.cs_current_bb _ = SOME bb` mp_tac >>
         qpat_assum `fn_has_code sm sb func` mp_tac >>
         rpt (pop_assum kall_tac) >>
         pure_rewrite_tac[fragExecTheory.fn_has_code_def] >> rpt strip_tac >>
         gvs[] >> fs[rich_listTheory.IS_PREFIX_APPEND] >>
         pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
         simp_tac (srw_ss()) []) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
        (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[EVERY_MEM] >> metis_tac[]) >>
      drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >> simp[]) >>
  all_tac >~ [`ghost_inv_at (DF H) _ _ _ _ _ _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- fs[Abbr `ff`]) >> strip_tac >>
      `local_ptrs_rel func cenv mid.scopes t` by
        fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
      `local_region cenv mid.scopes t id (w2n rootw) sz` by
        (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
      simp[Abbr `ff`] >>
      irule bodyFullMemoryFramesTheory.body_full_local_scope_ghost_post >>
      conj_tac >- fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
      conj_tac >- simp[] >>
      conj_tac >- (simp[ptrDisciplineTheory.allocas_from_def] >>
                    metis_tac[ptrDisciplineTheory.allocas_from_def]) >>
      conj_tac
      >- (qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _` mp_tac >>
          qpat_assum `u.vs_accounts = _` mp_tac >>
          qpat_assum `u.vs_transient = _` mp_tac >>
          qpat_assum `u.vs_immutables = _` mp_tac >>
          qpat_assum `u.vs_call_ctx = _` mp_tac >>
          qpat_assum `tnf.t_stor = _` mp_tac >>
          qpat_assum `tnf.t_trans = _` mp_tac >>
          qpat_assum `tnf.t_imm = _` mp_tac >>
          rpt (pop_assum kall_tac) >>
          pure_rewrite_tac[venomStateTheory.mstore_def, LET_THM] >>
          simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def,
                               bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
      qexistsl_tac [`G`, `rootw`, `func`, `type_memory_size entry.type`,
                    `rp`, `t`, `sa`, `sz`, `tn`] >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          `not_fresh_at sm x` by
            (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
          `lookup_var x u = lookup_var x t` by
            (drule_all append_nested_memory_reserved_lookup >>
             disch_then irule >> simp[]) >>
          qpat_x_assum `lookup_var x u = lookup_var x t` mp_tac >>
          qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
          simp[venomStateTheory.lookup_var_def]) >>
      conj_tac
      >- (gen_tac >> disch_tac >> conj_tac
          >- (simp[Abbr `out`, Abbr `stored`] >>
              dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
              fs[Abbr `slot`, valueEncodingTheory.type_memory_size_def] >>
              qpat_assum `type_memory_size tv = 32` (fn th =>
                qpat_x_assum `k + (_ * type_memory_size tv + 32) <= q`
                  (mp_tac o REWRITE_RULE [th])) >> decide_tac) >>
          fs[Abbr `slot`, valueEncodingTheory.type_memory_size_def] >>
          qpat_assum `type_memory_size tv = 32` (fn th =>
            qpat_x_assum `k + (_ * type_memory_size tv + 32) <= q`
              (mp_tac o REWRITE_RULE [th])) >> strip_tac >>
          `~(k + (w2n rootw + 32 * (LENGTH vs + 1)) <= i /\
              i < k + (w2n rootw + (32 * (LENGTH vs + 1) + 32)))` by decide_tac >>
          metis_tac[]) >>
      conj_tac
      >- (`0 < sz` by
            (qpat_x_assum `k + type_memory_size (ArrayTV tv (Dynamic cap)) <= _` mp_tac >>
             simp[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
          `lo <= w2n rootw` by
            (irule (INST_TYPE [alpha |-> ``:256``]
               bodyFullMemoryFramesTheory.body_full_local_region_lower_bound) >>
             goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
             goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
             goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
             qexistsl_tac [`DF H`, `H`, `func`] >> simp[]) >>
          simp[Abbr `out`, Abbr `stored`] >>
          dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
          fs[Abbr `slot`] >> decide_tac) >>
      qpat_x_assum `ghost_inv_at (DF H) lo d cenv cx mid G tn t` mp_tac >>
      simp_tac (srw_ss()) [ghost_inv_at_def] >>
      strip_tac >> simp[]) >>
  all_tac >~ [`lookup_var x _ = SOME w`]
  >- (`not_fresh_at sm x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      simp[venomStateTheory.lookup_var_def] >>
      metis_tac[venomStateTheory.lookup_var_def]) >>
  `not_fresh_at sm x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
  simp[]
QED

Finalise append_nested_memory_cont_full[local]

Theorem append_nested_storage_success_path:
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME w /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  cap < dimword (:256) /\ op_taint tn bop = {} /\ op_taint tn vop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo t /\ ~ctx_has_dalloca ctx /\ ~t.vs_halted /\
  fn_has_code sm sb func /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  len = w2n (if tr then tload slot t else sload slot t) /\ len < cap /\
  ~t.vs_call_ctx.cc_static ==>
  ?u Gf tf.
    gas_path_ptr D lo ctx func PG G tn t 0 Gf tf
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    state_frame u = state_frame
      (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w t)
       else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w t)) /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then
       tf.t_trans = key_update (key_update tn.t_trans (slot+n2w (1+len)) {}) slot {} /\
       tf.t_stor = tn.t_stor
     else
       tf.t_stor = key_update (key_update tn.t_stor (slot+n2w (1+len)) {}) slot {} /\
       tf.t_trans = tn.t_trans) /\
    (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) /\
    run_inst_seq (emitted_insts sm sb) t = OK u /\
    run_inst_seq_mem_ok (emitted_insts sm sb) t /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tf /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
      (emitted_insts sm sb) /\
    inst_extends sm sb /\ sb.cs_current_bb = sm.cs_current_bb
Proof
  strip_tac >>
  drule_all stmtAppendStoragePathPtrTheory.append_storage_word_suffix_code >>
  strip_tac >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [stmtSimAppendStorageTheory.compile_dynarray_append_word_parts]) >>
  strip_tac >>
  `(!x. bop = Var x ==> not_fresh_at sm x) /\
   w2n (if tr then tload slot t else sload slot t) < cap` by metis_tac[] >>
  drule_all appendStorageStageTransportPtrTheory.append_storage_guard_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `D`] strip_assume_tac) >>
  suspend "suffix"
QED

Resume append_nested_storage_success_path[suffix]:
  `sm.cs_next_var <= s3.cs_next_var /\
   (!x. lop = Var x ==> not_fresh_at s3 x)` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _` mp_tac >>
     qpat_assum `emit_op LT _ _ = _` mp_tac >>
     qpat_assum `emit_void ASSERT _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> simp[]) >>
  `!x. bop = Var x \/ lop = Var x \/ vop = Var x ==> not_fresh_at s3 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand bop t' = SOME slot /\ eval_operand vop t' = SOME w /\
   op_taint tn' bop = {} /\ op_taint tn' vop = {}` by
    (Cases_on `bop` >> Cases_on `vop` >>
     gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
  `~t'.vs_call_ctx.cc_static` by
    (qpat_assum `state_frame t' = state_frame t` mp_tac >>
     qpat_assum `~t.vs_call_ctx.cc_static` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality] >>
     metis_tac[]) >>
  drule_all appendStorageStageTransportPtrTheory.append_storage_suffix_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G'`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume append_nested_storage_success_path[compose]:
  imp_res_tac emitHelperPropsTheory.inst_extends_emit_op >>
  imp_res_tac emitHelperPropsTheory.inst_extends_emit_void >>
  `inst_extends sm s3 /\ inst_extends s3 sb` by
    metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `emitted_insts sm sb = emitted_insts sm s3 ++ emitted_insts s3 sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >>
     fs[emitHelperPropsTheory.inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm s3)` by
    fs[EVERY_MEM] >>
  `run_inst_seq (emitted_insts sm sb) t = OK t''` by
    (irule emitHelperPropsTheory.run_inst_seq_compose_ok >>
     qexistsl_tac [`t'`, `s3`] >> simp[]) >>
  drule_all emittedSeqComposePtrTheory.emitted_inst_seq_ptr_uniform_compose >>
  strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sb) t G9 tn9` by
    (first_x_assum (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]) >>
  suspend "lift"
QED

Resume append_nested_storage_success_path[lift]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA)
      (emitted_insts sm sb)` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     simp[EVERY_MEM] >> strip_tac >> gen_tac >> disch_tac >>
     first_x_assum drule >> strip_tac >> gvs[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t G9 tn9` by
    (irule fragGasCopyLoopTheory.inst_seq_ptr_lower_bound_transport >>
     simp[] >> qexists_tac `0` >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb)` by
    (qpat_assum `EVERY (\i. _ /\ _ /\ _ /\ _) (emitted_insts sm sb)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)) = 0` by
    (simp[LENGTH_NIL, FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  qexistsl_tac [`t''`, `G9`, `tn9`] >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  suspend "post"
QED

Resume append_nested_storage_success_path[post]:
  conj_tac
  >- (qpat_assum `state_frame t'' = _` mp_tac >>
      qpat_assum `state_frame t' = state_frame t` mp_tac >>
      qpat_assum `len = _` mp_tac >>
      rpt (pop_assum kall_tac) >> Cases_on `tr` >>
      pure_rewrite_tac[boolTheory.COND_CLAUSES] >>
      disch_then SUBST1_TAC >>
      rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
      rpt strip_tac >>
      fs[stateFrameTheory.state_frame_def, venomStateTheory.tstore_def,
         venomStateTheory.sstore_def, wordsTheory.WORD_ADD_ASSOC]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_assum `if tr then _ else _` mp_tac >>
      qpat_assum `tn'.t_stor = tn.t_stor` mp_tac >>
      qpat_assum `tn'.t_trans = tn.t_trans` mp_tac >>
      qpat_assum `len = _` mp_tac >>
      rpt (pop_assum kall_tac) >> Cases_on `tr` >>
      pure_rewrite_tac[boolTheory.COND_CLAUSES] >>
      disch_then SUBST1_TAC >>
      rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
      simp[wordsTheory.WORD_ADD_ASSOC]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s3 x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s3 x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      simp[venomStateTheory.lookup_var_def] >>
      metis_tac[venomStateTheory.lookup_var_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule bodyMemAppendFactsTheory.append_storage_word_suffix_mem_ok >>
     goal_assum (drule_at Any)) >>
  `inst_extends sm sb` by metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     simp[exprLoweringPropsTheory.same_blocks_def]) >>
  simp[] >> fs[EVERY_MEM] >> metis_tac[]
QED

Finalise append_nested_storage_success_path

Theorem append_nested_storage_abort_path:
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME w /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  cap < dimword (:256) /\ op_taint tn bop = {} /\ op_taint tn vop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo t /\ ~ctx_has_dalloca ctx /\ ~t.vs_halted /\
  fn_has_code sm sb func /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  len = w2n (if tr then tload slot t else sload slot t) /\ ~(len < cap) ==>
  ?u Gf tf.
    gas_path_ptr D lo ctx func PG G tn t 0 Gf tf (Abort Revert_abort u) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
    ?r j. u = r with vs_inst_idx := j /\
      run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort r /\
      run_inst_seq_mem_ok (emitted_insts sm sb) t /\
      (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tf) /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                 i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
        (emitted_insts sm sb) /\
      inst_extends sm sb /\ sb.cs_current_bb = sm.cs_current_bb
Proof
  strip_tac >>
  drule_all stmtAppendStoragePathPtrTheory.append_storage_word_suffix_code >> strip_tac >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [stmtSimAppendStorageTheory.compile_dynarray_append_word_parts]) >>
  strip_tac >>
  `(!x. bop = Var x ==> not_fresh_at sm x) /\
   ~(w2n (if tr then tload slot t else sload slot t) < cap)` by metis_tac[] >>
  drule_all appendStorageStageTransportPtrTheory.append_storage_guard_abort_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  imp_res_tac emitHelperPropsTheory.inst_extends_emit_op >>
  imp_res_tac emitHelperPropsTheory.inst_extends_emit_void >>
  `inst_extends sm s3 /\ inst_extends s3 sb` by
    metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `emitted_insts sm sb = emitted_insts sm s3 ++ emitted_insts s3 sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >>
     fs[emitHelperPropsTheory.inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm s3)` by
    fs[EVERY_MEM] >>
  `run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort t'` by
    simp[exprLoweringPropsTheory.run_inst_seq_append_err] >>
  drule_all emittedSeqComposePtrTheory.emitted_inst_seq_ptr_uniform_abort_extend >>
  strip_tac >>
  `inst_seq_ptr
      <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
      0 ctx func PG G tn (emitted_insts sm sb) t G' tn'` by
    (first_x_assum (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]) >>
  suspend "lift"
QED

Resume append_nested_storage_abort_path[lift]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA)
      (emitted_insts sm sb)` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     simp[EVERY_MEM] >> strip_tac >> gen_tac >> disch_tac >>
     first_x_assum drule >> strip_tac >> gvs[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t G' tn'` by
    (gen_tac >>
     irule fragGasCopyLoopTheory.inst_seq_ptr_lower_bound_transport >>
     simp[] >> qexists_tac `0` >> simp[] >>
     irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >>
     simp[ptrDisciplineTheory.allocas_from_def] >> qexists_tac
       `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>` >>
     simp[] >> metis_tac[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t G' tn'` by simp[] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (qpat_assum `EVERY (\i. _ /\ _ /\ _ /\ _) (emitted_insts sm sb)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all stmtAppendStoragePathPtrTheory.run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  qexistsl_tac [`t' with vs_inst_idx := j`, `G'`, `tn'`] >>
  simp[] >> qexists_tac `j` >> simp[] >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule bodyMemAppendFactsTheory.append_storage_word_suffix_mem_ok >>
     goal_assum (drule_at Any)) >>
  `inst_extends sm sb` by metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     simp[exprLoweringPropsTheory.same_blocks_def]) >>
  simp[] >> fs[EVERY_MEM] >> metis_tac[]
QED

Finalise append_nested_storage_abort_path

Theorem append_nested_storage_endpoint_full:
  stmt_state_rel H ctx func cenv cx mid t /\
  storage_well_formed_on cx mid (FST H) /\
  ghost_inv_at D lo d cenv cx mid G tn t /\
  dead_lo_ok H D lo cenv cx /\
  return_buf_frame d cenv sm t /\
  regions_consistent (FST H) /\
  MEM (tr,rootk,root) (FST H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  type_slot_size tv = 1 /\ len < cap /\
  well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
  value_has_type tv v /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid = (INL (),ee) /\
  ee = set_storage cx mid tr
    (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr))) /\
  state_frame u = state_frame
    (if tr then tstore slot (n2w (len+1))
       (tstore (slot+n2w (1+len)) w t)
     else sstore slot (n2w (len+1))
       (sstore (slot+n2w (1+len)) w t)) /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then
     tf.t_trans = key_update (key_update tn.t_trans (slot+n2w (1+len)) {}) slot {} /\
     tf.t_stor = tn.t_stor
   else
     tf.t_stor = key_update (key_update tn.t_stor (slot+n2w (1+len)) {}) slot {} /\
     tf.t_trans = tn.t_trans) /\
  (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==> not_fresh_at sb x) /\
  z = (u with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  stmt_state_rel H ctx func cenv cx ee z /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at D lo d cenv cx ee Gf tf z /\
  return_buf_frame d cenv sb z /\
  z.vs_alloca_next = t.vs_alloca_next /\
  z.vs_allocas = t.vs_allocas /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t)
Proof
  strip_tac >>
  conj_tac >- suspend "state_rel" >>
  conj_tac >- (irule vyperFiniteStoragePreservationTheory.append_subregion_preserves_storage_well_formed_on >>
    goal_assum (drule_at Any) >> metis_tac[]) >>
  conj_tac >- suspend "ghost" >>
  suspend "frames"
QED

Resume append_nested_storage_endpoint_full[state_rel]:
  drule_all appendResolvedStorageRelTheory.stmt_state_rel_append_resolved_storage_updates >>
  disch_then (qspec_then `w` mp_tac) >>
  strip_tac >>
  irule assignTuplePtrLoadStepTheory.stmt_state_rel_old_vars_frame_ptr >>
  goal_assum (drule_at Any) >>
  qexists_tac `if tr then tstore slot (n2w (len+1))
       (tstore (slot+n2w (1+len)) w t)
     else sstore slot (n2w (len+1))
       (sstore (slot+n2w (1+len)) w t)` >>
  conj_tac >- (Cases_on `tr` >>
    simp[venomStateTheory.lookup_var_def, venomStateTheory.tstore_def,
         venomStateTheory.sstore_def] >>
    metis_tac[venomStateTheory.lookup_var_def]) >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  suspend "state_frame"
QED

Resume append_nested_storage_endpoint_full[state_frame]:
  gvs[]
QED

Resume append_nested_storage_endpoint_full[ghost]:
  Cases_on `tr` >>
  (gvs[stateFrameTheory.state_frame_def, venomStateTheory.tstore_def,
       venomStateTheory.sstore_def] >>
   `!p sz. not_fresh_at sm p /\ ptr_covers G tn p t sz ==>
       ptr_covers Gf tf p (u with vs_inst_idx := LENGTH sb.cs_current_insts) sz` by
     (rw[bodyPtrDefsTheory.ptr_covers_def] >>
      gvs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
   gvs[bodyPtrDefsTheory.ghost_inv_at_def,
       vyperStorageBackendTheory.set_storage_def] >>
   conj_tac
   >- (rpt gen_tac >> strip_tac >>
       rename1 `lookup_scopes name mid.scopes = SOME entry` >>
       `not_fresh_at sm p` by
         metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
       gvs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
   conj_tac
   >- (Cases_on `d` >> gvs[bodyPtrDefsTheory.return_buf_ptr_def] >>
       rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
       gvs[bodyPtrDefsTheory.return_buf_ptr_def,
           venomStateTheory.lookup_var_def] >> metis_tac[])) >>
  rpt conj_tac >>
  gvs[ptrDisciplineTheory.allocas_from_def] >>
  suspend "storage_taint"
QED

Resume append_nested_storage_endpoint_full[storage_taint]:
  markerLib.RESUME_TAC >>
  gvs[bodyPtrDefsTheory.stor_taint_ok_at_def,
      bodyPtrDefsTheory.dead_lo_ok_def, sourceUnitExecutionTheory.cx_dead_def] >>
  Cases_on `t.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
      ptrDisciplineTheory.key_update_def, pred_setTheory.SUBSET_DEF,
      pred_setTheory.IN_DIFF] >>
  rpt strip_tac >> gvs[] >>
  irule (SRULE [arithmeticTheory.ADD_COMM]
    appendResolvedStorageRelTheory.append_resolved_storage_dead_mono) >>
  conj_tac >- metis_tac[] >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Resume append_nested_storage_endpoint_full[frames]:
  Cases_on `tr` >>
  gvs[stateFrameTheory.state_frame_def, venomStateTheory.tstore_def,
      venomStateTheory.sstore_def] >>
  (simp[venomStateTheory.lookup_var_def] >>
   conj_tac
   >- (Cases_on `d` >> gvs[loweringPostsTheory.return_buf_frame_def] >>
       rename1 `return_buf_frame (SOME rb)` >> PairCases_on `rb` >>
       gvs[loweringPostsTheory.return_buf_frame_def] >>
       gvs[venomStateTheory.lookup_var_def]) >>
   gvs[venomStateTheory.lookup_var_def])
QED

Finalise append_nested_storage_endpoint_full

Theorem append_nested_storage_cont_full:
 !DF lo d ctx shadow_ctx PG func cx st0 lctx RetQ cenv env sa sm sb s0 G0 tn0
   mid t G tn tr slot tv v bop vop w elem src_ty cap.
  body_inv (cx_tops cx) ctx cenv cx /\
  gas_admissible (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v)
    (stmt_res_ok lctx) mid /\
  expr_sim_inv cenv cx env mid /\ supported_full_word_type elem /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  value_has_type tv v /\ abi_tuple_word tv v /\
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME w /\
  w = typed_val_to_w256 tv v /\
  op_taint tn bop = {} /\ op_taint tn vop = {} /\ cap < dimword (:256) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
    storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct func /\ fn_has_code sm sb func /\
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sm t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v) (mid,t,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
         op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s))
Proof
  rpt gen_tac >> strip_tac >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x` by
    (metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base,
               freshWritesTheory.not_fresh_at_mono]) >>
  suspend "classify"
QED

Resume append_nested_storage_cont_full[classify]:
  `is_word_type elem` by
    fs[supportedTypesTheory.supported_full_word_type_def, compileEnvTheory.is_word_type_def] >>
  `type_slot_size tv = 1` by metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  `encode_value tv v = SOME [(0,typed_val_to_w256 tv v)]` by
    metis_tac[stmtSimAssignStorageFactsTheory.encode_value_word_typed] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  strip_tac >>
  `t.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def] >>
  `!raw. storage_read_live (storage_trace_horizon mid.storage_trace) tr raw slot
      (ArrayTV tv (Dynamic cap))` by
    (gen_tac >> irule accountsRelPropsTheory.storage_place_observed_read_live >>
     simp[vyperValueTheory.type_slot_size_def]) >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)` by
    (fs[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
     `regions_consistent (FST (storage_trace_horizon mid.storage_trace))` by
       (fs[vyperStorageFootprintTheory.storage_trace_domain_def,
           vyperStorageFootprintTheory.valid_horizon_def]) >>
     drule_then assume_tac vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
     `w2n root + type_slot_size tv' <= dimword (:256)` by
       metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
     `w2n root + delta < dimword (:256)` by
       (fs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
     `delta < dimword (:256)` by decide_tac >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  `(if tr then tload slot t else sload slot t) =
      lookup_storage slot (get_storage cx mid tr)` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       (cj 2 targetSubscriptStorageTheory.target_storage_array_len_ok)) >>
     conj_tac >- (qexists_tac `bop` >> simp[]) >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `cenv`, `ctx`, `func`,
                   `cap`, `tv`] >> simp[]) >>
  `key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       appendStorageGhostPtrTheory.storage_dead_key_taint_empty) >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`,
       `if tr then contract_transient t else contract_storage t`, `tr`,
       `ArrayTV tv (Dynamic cap)`] >>
     simp[vyperValueTheory.type_slot_size_def] >>
     qpat_assum `!H. dead_lo_ok H _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` assume_tac) >>
     Cases_on `t.vs_call_ctx.cc_address = cx.txn.target` >>
     Cases_on `tr` >>
     fs[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
        bodyPtrDefsTheory.dead_lo_ok_def,
        sourceUnitExecutionTheory.cx_dead_def, venomStateTheory.contract_storage_def,
        venomStateTheory.contract_transient_def, vfmStateTheory.lookup_account_def]) >>
  Cases_on `w2n (lookup_storage slot (get_storage cx mid tr)) < cap`
  >- suspend "success"
  >> suspend "capacity"
QED

Resume append_nested_storage_cont_full[success]:
  Cases_on `cx.txn.is_static` >- suspend "static" >>
  `~t.vs_call_ctx.cc_static` by simp[] >>
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx mid tr))` >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
   (INL (), set_storage cx mid tr
      (update_storage slot (n2w (len+1))
        (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr))))` by
    (mp_tac (Q.INST [`len` |-> `len`, `es` |-> `mid`, `w` |-> `w`]
       vyperStorageBackendTheory.append_storage_word_success) >>
     (impl_tac >- simp[Abbr `len`]) >>
     Cases_on `tr` >>
     simp[vyperStorageBackendTheory.set_storage_def]) >>
  suspend "source_success"
QED

Resume append_nested_storage_cont_full[source_success]:
  `allocas_from lo t` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `len = w2n (if tr then tload slot t else sload slot t)` by simp[Abbr `len`] >>
  drule_all append_nested_storage_success_path >>
  disch_then (qspecl_then [`PG`, `G`, `DF (storage_trace_horizon mid.storage_trace)`]
    strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tf` by
    (gen_tac >> drule_all append_nested_storage_success_path >>
     disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)` by
    (rpt gen_tac >> irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     conj_tac >- simp[] >> qexists_tac `sm` >>
     simp[] >> fs[EVERY_MEM]) >>
  drule_all stmtAppendStoragePathPtrTheory.append_storage_word_suffix_code >> strip_tac >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`alloca_inv t` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     `?rest. DROP t.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest` by
       metis_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >> simp[]) >>
  qmatch_asmsub_abbrev_tac `append_place _ _ _ mid = (INL (),ee)` >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
      (mid with gas_obs := tail) = (INL (),ee with gas_obs := tail)` by
    (gen_tac >> mp_tac (Q.INST [`len` |-> `len`,
       `es` |-> `mid with gas_obs := tail`, `w` |-> `w`]
       vyperStorageBackendTheory.append_storage_word_success) >>
     (impl_tac >- (Cases_on `tr` >> simp[Abbr `len`, vyperStorageBackendTheory.get_storage_def])) >>
     Cases_on `tr` >> simp[Abbr `ee`, vyperStorageBackendTheory.set_storage_def,
       vyperStorageBackendTheory.get_storage_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  conj_tac >- (qexistsl_tac [`Gf`, `ee`, `INL ()`,
     `u with vs_inst_idx := LENGTH sb.cs_current_insts`, `tf`] >>
     simp[] >> gen_tac >> disch_tac >>
     `ee.storage_trace = mid.storage_trace /\ ee.scopes = mid.scopes` by
       (Cases_on `tr` >> simp[NoAsms, Abbr `ee`, vyperStorageBackendTheory.set_storage_def]) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- fs[]) >> strip_tac >>
     `regions_consistent (FST H)` by
       fs[vyperStorageFootprintTheory.valid_horizon_def] >>
     qpat_assum `storage_place_observed H _`
       (strip_assume_tac o PURE_REWRITE_RULE
          [vyperStoragePlaceObservedTheory.storage_place_observed_def]) >>
     `w2n root + type_slot_size tv' <= dimword (:256)` by
       metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
     `w2n slot = w2n root + delta` by
       (drule_then assume_tac vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
        `w2n root + delta < dimword (:256)` by
          (fs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
        `delta < dimword (:256)` by decide_tac >>
        simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
     `well_formed_type_value (ArrayTV tv (Dynamic cap))` by
       (`well_formed_type_value tv` by
          metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
        simp[vyperTypingTheory.well_formed_type_value_def,
          vyperValueTheory.type_slot_size_def]) >>
     `local_ptrs_reserved cenv sm /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
      (!x. not_fresh_at sm x ==> not_fresh_at sb x)` by
       (conj_tac >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
          qexists_tac `sa` >> simp[]) >>
        `sm.cs_next_var <= sb.cs_next_var` by
          metis_tac[bodyMemAppendFactsTheory.append_storage_word_suffix_grows_mem] >>
        metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     `ee = set_storage cx mid tr (update_storage slot (n2w (len+1))
         (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr)))` by
       simp[Abbr `ee`] >>
     `dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
     rename1 `MEM (tr,rk,tv') (FST H)` >>
     mp_tac (Q.INST [`z` |-> `u with vs_inst_idx := LENGTH sb.cs_current_insts`,
        `D` |-> `DF H`, `rootk` |-> `rk`, `root` |-> `tv'`]
        append_nested_storage_endpoint_full) >>
     (impl_tac >- (rpt conj_tac >> rewrite_tac[] >> first_assum ACCEPT_TAC)) >>
     strip_tac >>
     `u.vs_current_bb = t.vs_current_bb /\ u.vs_halted = t.vs_halted` by
       (qpat_x_assum `state_frame u = _` mp_tac >> Cases_on `tr` >>
        simp[NoAsms, stateFrameTheory.state_frame_def,
          venomStateTheory.tstore_def, venomStateTheory.sstore_def,
          venomStateTheory.venom_state_component_equality]) >>
     conj_tac >- simp[loweringPostsTheory.stmt_lands_def] >>
     conj_tac >- simp[] >>
     conj_tac >- metis_tac[bodyMemAppendFactsTheory.append_storage_word_suffix_open_mem] >>
     conj_tac >- simp[loweringPostsTheory.cenv_top_ext_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (`storage_well_formed_on cx (ee with gas_obs := []) (FST H) <=>
                    storage_well_formed_on cx ee (FST H)` by
        (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
         simp[NoAsms]) >> asm_rewrite_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_x_assum `(_ with vs_inst_idx := _).vs_alloca_next = _` mp_tac >>
        simp_tac (srw_ss()) [] >> disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gf tf _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def,
          bodyPtrDefsTheory.stor_taint_ok_at_def] >> metis_tac[]) >>
     `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qpat_x_assum `(_ with vs_inst_idx := _).vs_allocas = _` mp_tac >>
        simp_tac (srw_ss()) [] >> disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     metis_tac[]) >> simp[]
QED

Resume append_nested_storage_cont_full[capacity]:
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
     (INR (Error (RuntimeError "append full storage array")),mid)` by
    (irule vyperStorageBackendTheory.append_storage_full >> decide_tac) >>
  `allocas_from lo t` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  mp_tac (Q.INST [`D` |->
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`,
    `len` |-> `w2n (lookup_storage slot (get_storage cx mid tr))`]
    append_nested_storage_abort_path) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >>
  drule_all stmtAppendStoragePathPtrTheory.append_storage_word_suffix_code >>
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all bodyUnopFragMemoryTheory.run_inst_seq_abort_zero_path_mem >>
  strip_tac >>
  fs[fragGasModeTheory.gas_marked_path_def] >>
  suspend "capacity_joint"
QED

Resume append_nested_storage_cont_full[capacity_joint]:
  first_x_assum (qspec_then `ctx` (qx_choose_then `jm` assume_tac)) >>
  `r with vs_inst_idx := jm = r with vs_inst_idx := j` by
    (qpat_assum `gas_path_mem _ _ _ _ _` mp_tac >>
     qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule gasPathPtrExecTheory.gas_path_ptr_exec >>
     simp[fragExecTheory.exit_result_def] >> strip_tac >>
     drule fragGasPathMemTheory.gas_path_mem_exec >>
     simp[fragExecTheory.exit_result_def] >> strip_tac >>
     `run_from (fuel + fuel') ctx func t = Abort Revert_abort (r with vs_inst_idx := j)` by
       (irule fragGasPathTheory.gas_run_from_fuel_mono >>
        conj_tac >- simp[] >> qexists_tac `fuel` >> simp[]) >>
     `run_from (fuel + fuel') ctx func t = Abort Revert_abort (r with vs_inst_idx := jm)` by
       (irule fragGasPathTheory.gas_run_from_fuel_mono >>
        conj_tac >- simp[] >> qexists_tac `fuel'` >> simp[]) >> gvs[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort (r with vs_inst_idx := j),Gf,tf)` by
    (gen_tac >> irule fragGasOriginPtrExecTheory.gas_zero_paths_joint >>
     simp[fragExecTheory.exit_result_def] >>
     conj_tac >- metis_tac[] >>
     irule ptrSafetyTransportTheory.gas_path_ptr_from_no_dead >> first_assum ACCEPT_TAC) >>
  suspend "capacity_exit"
QED

Resume append_nested_storage_cont_full[capacity_exit]:
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
       (mid with gas_obs := tail) =
     (INR (Error (RuntimeError "append full storage array")),mid with gas_obs := tail)` by
    (gen_tac >> irule vyperStorageBackendTheory.append_storage_full >>
     Cases_on `tr` >>
     fs[vyperStorageBackendTheory.get_storage_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gf`, `mid`, `Abort Revert_abort (r with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "append full storage array"))`, `tf`] >>
  simp[fragExecTheory.exit_result_def, bodyPtrDefsTheory.stmt_exit_ptr_def,
    exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >> simp[]
QED

Resume append_nested_storage_cont_full[static]:
  `allocas_from lo t` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `w2n (if tr then tload slot t else sload slot t) < cap` by simp[] >>
  `t.vs_call_ctx.cc_static` by simp[] >>
  drule_all appendStorageStaticPtrTheory.append_storage_word_static_origin_path >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
      (mid with gas_obs := tail) =
      (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)` by
    (gen_tac >> irule stmtSimAppendStorageTheory.append_storage_static >>
     Cases_on `tr` >> gvs[vyperStorageBackendTheory.get_storage_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gf`, `mid`,
    `Abort ExHalt_abort ((halt_state (set_returndata [] u)) with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "write in static context"))`, `tf`] >>
    simp[fragExecTheory.exit_result_def, bodyPtrDefsTheory.stmt_exit_ptr_def,
      exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >> simp[]
QED

Finalise append_nested_storage_cont_full

Theorem append_nested_after_target_full[local]:
  supported_stmt (cx_tops cx) bindings (Append bt e) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  body_inv (cx_tops cx) ctx cenv cx /\
  supported_full_word_type (expr_type e) /\
  expr_body_pre cenv cx env e es /\ target_pre cenv cx env bt es /\
  body_expr_full_ok cx e /\
  eval_target_place cx bt (es with gas_obs := gs) = (INL place,mid) /\
  return_buf_frame d cenv sp t /\ ~t.vs_halted /\
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx))
    (append_place cx place)) (stmt_res_ok lctx) mid /\
  type_place_target env bt = SOME (Type (ArrayT (expr_type e) (Dynamic cap))) /\
  stmt_env cenv lctx ret_ty (Append bt e) sa = (cenv,sb) /\
  stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append bt e)) shadow_sa = (cenv,shadow_sb) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  compile_get_target_ptr compile_expr cenv (gas_shadow_target bt) shadow_sa = (r,shadow_sp) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sp shadow_sp /\
  gas_shadow_state sb shadow_sb /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sp sb func /\ fn_has_code shadow_sp shadow_sb shadow_func /\
  ci_mono sa sp /\ ci_mono sp sb /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    target_post H ctx func cenv cx es sa sp s0 mid (PlaceR place)
      (Type (ArrayT (expr_type e) (Dynamic cap))) r t /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
    target_ptr_ok cenv (PlaceR place) r G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
  (!id path. place = MemoryPlace id path ==>
    ?entry v. lookup_scopes id mid.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  t.vs_current_bb = sp.cs_current_bb /\ t.vs_inst_idx = LENGTH sp.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx place)) (mid,t,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
         op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt q.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt q) /\
      halt_exit H cx ee res q /\
      (ctx_has_dalloca ctx ==> !s.
        (q = Halt s \/ ?ir. q = IntRet ir s) ==> allocas_below_fmp s))
Proof
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  PairCases_on `r` >>
  fs[loweringPostsTheory.target_post_def, value_type_place_def] >>
  `?loc. r1 = SOME loc` by
    (Cases_on `place` >> fs[place_ptr_rel_def]) >>
  gvs[] >>
  `is_word_type (expr_type e)` by
    fs[supported_full_word_type_def, is_word_type_def] >>
  drule_all stmtSimAppendResolvedTheory.append_resolved_word_code_parts >> strip_tac >>
  `expr_body_pre cenv cx env e mid` by
    (irule append_resolved_rhs_body_pre >>
     goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sp` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) _ = (shadow_op,shadow_sm)` >>
  `shadow_op = vop /\ gas_shadow_state sm shadow_sm` by
    (qspec_then `expr_type e` mp_tac (Q.GEN `ty` gas_shadow_stmt_lower_value) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sp`,`shadow_sp`] mp_tac) >> simp[]) >>
  `ci_mono sm sb` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ sm = _`
       (mp_tac o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     pure_rewrite_tac [pairTheory.SND] >> disch_then (SUBST1_TAC o SYM) >>
     irule ci_mono_compile_dynarray_append) >>
  `ci_mono sp sm` by
    (qpat_assum `lower_value _ _ _ e sp = _`
       (mp_tac o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     pure_rewrite_tac [pairTheory.SND] >> disch_then (SUBST1_TAC o SYM) >>
     irule ci_mono_lower_value_compile_expr) >>
  `fn_has_code sp sm func /\ fn_has_code sm sb func` by
    (irule fragExecTheory.fn_has_code_split >> fs[ci_mono_def]) >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o REWRITE_RULE [gasShadowTheory.gas_shadow_stmt_def]) >>
  `ci_mono shadow_sm shadow_sb` by
    (drule stmtSimAppendResolvedTheory.append_resolved_word_code_parts >>
     simp[] >> strip_tac >>
     metis_tac [ci_mono_compile_dynarray_append, pairTheory.SND]) >>
  `ci_mono shadow_sp shadow_sm` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sp = _`
       (mp_tac o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     pure_rewrite_tac [pairTheory.SND] >> disch_then (SUBST1_TAC o SYM) >>
     irule ci_mono_lower_value_compile_expr) >>
  `fn_has_code shadow_sp shadow_sm shadow_func` by
    (fs[ci_mono_def] >> metis_tac [fragExecTheory.fn_has_code_split]) >>
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> fs[ci_mono_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x)` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e mid` by
    (fs[body_expr_full_ok_def] >> first_x_assum (irule o cj 1) >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac [expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sp`,`sm`,`shadow_sp`,`shadow_sm`,`vop`,`t`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    drule_all contextRawReachableTheory.frag_reachable_members >> strip_tac >>
    `inst.inst_opcode <> DALLOCA` by
      (qpat_x_assum `~ctx_has_dalloca ctx` mp_tac >>
       qpat_x_assum `MEM fn ctx.ctx_functions` mp_tac >>
       qpat_x_assum `MEM inst (fn_insts fn)` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[ptrDisciplineTheory.ctx_has_dalloca_def, EXISTS_MEM] >>
       metis_tac[]) >>
    simp[unitMemInvTheory.dalloca_no_wrap_def])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 R1` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_value] >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn t. Q1 H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rhs_exit" >>
  simp[Abbr `Q1`] >> suspend "suffix"
QED

Resume append_nested_after_target_full[rhs_exit]:
  simp[Abbr `R1`] >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >> Cases_on `r` >> gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def,
      exprSimDefsTheory.halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def]
QED

Resume append_nested_after_target_full[suffix]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE [])) >>
  `expr_sim_inv cenv cx env mid' /\ value_runtime_typed env (expr_type e) v` by
    (`expr_sim_inv cenv cx env (mid' with gas_obs := []) /\
      value_runtime_typed env (expr_type e) v` by
       (`expr_body_pre cenv cx env e
           (mid with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
        qpat_x_assum `expr_body_pre _ _ _ _ (_ with gas_obs := _)` mp_tac >>
        qpat_x_assum `bind (eval_expr cx e) (read_result cx)
          (mid with gas_obs := _) = _` mp_tac >>
        qpat_x_assum `res = INL v` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
        drule_at (Pat `bind _ _ _ = _`)
          (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >>
        disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
        simp[vyperTypeExprResultTheory.expr_result_typed_def,
             vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
             vyperTypeInvariantsTheory.value_result_typed_def,
             vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >> fs[]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
     expr_post H ctx func cenv cx e mid sp sm t mid' v vop t' /\
     ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t'` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[] >> metis_tac[sumTheory.INL_11]) >>
  `(!x w. not_fresh_at sp x /\ lookup_var x t = SOME w ==> lookup_var x t' = SOME w) /\
   (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP t'.vs_allocas aid = SOME b)` by
    fs[expr_post_def] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sp.cs_next_var <= sm.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `return_buf_frame d cenv sm t'` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`t`,`sp`] >> simp[]) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t' = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t'.vs_allocas aid = SOME b) /\
   (!x. not_fresh_at sa x ==> FLOOKUP G1 x = FLOOKUP G0 x /\
     op_taint tn1 (Var x) = op_taint tn0 (Var x))` by
    (fs[ghost_kept_at_def] >> rpt strip_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def]) >>
  `gas_admissible (append_place cx place v) (stmt_res_ok lctx) mid'` by
    (`gas_admissible (append_place cx place v) (stmt_res_ok lctx)
        (mid' with gas_obs := [])` suffices_by simp[] >>
     irule stmtSimForRoundsTheory.gas_admissible_bind_tail >>
     qexistsl_tac [`bind (eval_expr cx e) (read_result cx)`, `mid`,
                  `gas_explicit marks t.vs_gas_readings`] >> simp[]) >>
  `place_ptr_rel cenv cx t' (PlaceR place) w (SOME loc)
     (Type (ArrayT (expr_type e) (Dynamic cap)))` by
    (Cases_on `place` >> fs[place_ptr_rel_def] >>
     `not_fresh_at sp p` by
       (qpat_x_assum `local_ptrs_reserved cenv sp` mp_tac >>
        simp[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
     qpat_x_assum `!x w. not_fresh_at sp x /\ lookup_var x t = SOME w ==> _` irule >> simp[]) >>
  `target_ptr_ok cenv (PlaceR place)
     (r0,SOME loc,SOME (ValPT (ArrayT (expr_type e) (Dynamic cap)))) G1 tn1 t'` by
    (qpat_assum `target_ptr_ok _ _ _ G tn t` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv mid sp G tn t G1 tn1` mp_tac >>
     qpat_assum `!x. r0 = Var x ==> not_fresh_at sp x` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sp` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyFullTargetDefsTheory.target_ptr_ok_def, ghost_kept_at_def,
          loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     rpt strip_tac >> Cases_on `r0` >>
     gvs[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def] >>
     metis_tac[]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         value_has_type tv v /\ type_memory_size tv = 32 /\ abi_tuple_word tv v` by
    (qpat_assum `value_runtime_typed env (expr_type e) v` mp_tac >>
     qpat_assum `supported_full_word_type (expr_type e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rw[supported_full_word_type_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        evaluate_type_def] >>
     Cases_on `v` >>
     gvs[evaluate_type_def, valueEncodingTheory.type_memory_size_def,
         abiTuplePropsTheory.abi_tuple_word_def, vyperTypingTheory.value_has_type_def]) >>
  `eval_operand vop t' = SOME (typed_val_to_w256 tv v)` by
    (drule_all exprSimPrecompilesTheory.expr_post_typed_stack_operand >> simp[]) >>
  `op_taint tn1 vop = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `!x. vop = Var x ==> not_fresh_at sm x` by
    (drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> simp[]) >>
  `runtime_place_typed cx mid place (ArrayTV tv (Dynamic cap)) /\
   runtime_place_writable cx mid place /\ storage_place_region cx place` by
    (`target_pre cenv cx env bt (es with gas_obs := gs)` by fs[] >>
     `well_typed_target env bt (ArrayT (expr_type e) (Dynamic cap))` by
       fs[vyperTypeSystemTheory.well_typed_target_def] >>
     `env_consistent env cx (es with gas_obs := gs) /\
      state_well_typed (es with gas_obs := gs) /\ context_well_typed cx /\
      accounts_well_typed (es with gas_obs := gs).accounts /\
      functions_well_typed cx /\ env.type_defs = get_tenv cx` by
       (fs[targetPlaceSimTheory.target_pre_def, expr_sim_inv_def] >>
        gvs[vyperTypeInvariantsTheory.env_consistent_def,
            vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     drule_all exprSimPopNestedLocalSourceTheory.eval_target_place_runtime_facts >>
     strip_tac >>
     `evaluate_type (get_tenv cx) (ArrayT (expr_type e) (Dynamic cap)) =
        SOME (ArrayTV tv (Dynamic cap))` by
       (qpat_x_assum `eval_result_typed _ _ _` mp_tac >>
        simp[vyperPlaceResultTypingTheory.eval_result_typed_place,
             evaluate_type_def, AllCaseEqs()]) >>
     drule_all tuplePlaceSourceHeadTheory.tuple_place_source_target_endpoint >> simp[]) >>
  `mid'.scopes = mid.scopes` by
    (`supported_pure_expr (cx_tops cx) e` by fs[supported_stmt_def] >>
     qpat_assum `bind (eval_expr cx e) (read_result cx)
       (mid with gas_obs := gas_explicit marks t.vs_gas_readings) = _` mp_tac >>
     qpat_assum `supported_pure_expr _ e` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac (cj 1 stmtSimForArrayFrameTheory.supported_pure_scopes_mutual) >>
     imp_res_tac vyperScopePreservationTheory.read_result_scopes >> gvs[]) >>
  Cases_on `place`
  >- suspend "storage"
  >- suspend "memory" >>
  fs[loweringPostsTheory.place_ptr_rel_def]
QED

Resume append_nested_after_target_full[memory]:
  rename1 `MemoryPlace id path` >>
  `?entry. lookup_scopes id mid'.scopes = SOME entry /\ entry.assignable` by
    (fs[vyperPlaceWriteSoundnessTheory.runtime_place_writable_def] >> metis_tac[]) >>
  `?old. evaluate_subscripts entry.type entry.value path = INL old` by
    ((gvs[])) >>
  qpat_assum `place_ptr_rel _ _ t' _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [loweringPostsTheory.place_ptr_rel_def] >>
  strip_tac >>
  `entry.type = tv0` by
    (qpat_assum `expr_sim_inv _ _ _ mid'` mp_tac >>
     qpat_assum `lookup_scopes id mid'.scopes = SOME entry` mp_tac >>
     qpat_assum `cenv.ce_var_type id = SOME t0` mp_tac >>
     qpat_assum `evaluate_type _ t0 = SOME tv0` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
     rpt strip_tac >>
     `IS_SOME (FLOOKUP env.var_types id)` by metis_tac[] >>
     Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
     qpat_assum `!id ty. _ ==> cenv.ce_var_type id = SOME ty` drule >>
     strip_tac >> gvs[] >>
     qpat_assum `!id ty entry. _ /\ _ ==> evaluate_type _ _ = _` drule >>
     simp[]) >>
  `tv' = ArrayTV tv (Dynamic cap)` by
    (qpat_assum `evaluate_type _ (ArrayT _ _) = SOME tv'` mp_tac >>
     qpat_assum `evaluate_type _ (expr_type e) = SOME tv` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule vyperTypeEnvTheory.scope_well_typed_lookup_scopes >>
     goal_assum (drule_at Any) >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.state_well_typed_def]) >>
  `value_has_type (ArrayTV tv (Dynamic cap)) old` by
    (irule vyperPlaceStatePreservationTheory.evaluate_subscripts_type >>
     goal_assum (drule_at Any) >>
     metis_tac[exprSimPropsTheory.mem_path_offset_sound]) >>
  `?vs. old = ArrayV (DynArrayV vs)` by
    (qpat_x_assum `value_has_type (ArrayTV _ _) old` mp_tac >>
     Cases_on `old` >> simp[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def]) >>
  `stmt_state_rel (storage_trace_horizon mid'.storage_trace)
     ctx func cenv cx mid' t'` by fs[expr_post_def] >>
  `local_ptrs_rel func cenv mid'.scopes t'` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid' t'` mp_tac >>
     simp_tac (srw_ss()) [exprLoweringPropsTheory.stmt_state_rel_def,
                         loweringStateRelDefsTheory.state_rel_def] >>
     metis_tac[]) >>
  `w2n b + sz <= t'.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
     disch_then (qspecl_then [`id`, `entry`, `p`, `sz`] mp_tac o CONJUNCT1) >>
     simp[] >> metis_tac[]) >>
  `ptr_covers G1 tn1 p t' sz /\
   (!m. mem_agree_outside tn1.t_mem t'.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n b) m)` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid' G1 tn1 t'` mp_tac >>
     pure_rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
     disch_then (qspecl_then [`id`, `entry`, `p`, `sz`] mp_tac o CONJUNCT1) >>
     simp[] >> metis_tac[]) >>
  `(!m. mem_agree_outside tn1.t_mem t'.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
        (w2n b+k) m) /\
   (!i. w2n b+k <= i /\ i < w2n b+k+32 ==> i NOTIN tn1.t_mem)` by
    (irule append_nested_robust_array_project >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `k + 32*(1+cap) <= sz` by
    (drule exprSimPropsTheory.mem_path_offset_sound >>
     simp[valueEncodingTheory.type_memory_size_def] >> strip_tac >>
     `type_memory_size tv0 <= sz` by metis_tac[] >> decide_tac) >>
  `t'.vs_alloca_next < dimword (:256)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def,
        exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `w2n b+k < dimword (:256)` by decide_tac >>
  `w2n w = w2n b+k` by
    (`k < dimword (:256)` by decide_tac >>
     asm_rewrite_tac[] >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
  `op_prov G1 r0 = FLOOKUP G1 p /\ op_taint tn1 r0 = {}` by
    (qpat_assum `target_ptr_ok _ _ _ G1 tn1 t'` mp_tac >>
     qpat_assum `FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[bodyFullTargetDefsTheory.target_ptr_ok_def] >> metis_tac[]) >>
  `?q. r0 = Var q` by
    (qpat_assum `ptr_covers G1 tn1 p t' sz` mp_tac >>
     qpat_assum `op_prov G1 r0 = FLOOKUP G1 p` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `r0` >>
     simp[bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_prov_def] >>
     metis_tac[]) >>
  `not_fresh_at sm q /\ lookup_var q t' = SOME w` by
    (`not_fresh_at sp q` by metis_tac[] >>
     `not_fresh_at sm q` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >>
        goal_assum (drule_at Any) >> simp[]) >>
     fs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `ptr_covers G1 tn1 q t' (32*(1+cap))` by
    (qpat_assum `ptr_covers G1 tn1 p t' sz` mp_tac >>
     qpat_assum `op_prov G1 r0 = FLOOKUP G1 p` mp_tac >>
     qpat_assum `op_taint tn1 r0 = {}` mp_tac >>
     qpat_assum `r0 = Var q` mp_tac >>
     qpat_assum `lookup_var p t' = SOME b` mp_tac >>
     qpat_assum `lookup_var q t' = SOME w` mp_tac >>
     qpat_assum `w2n w = w2n b+k` mp_tac >>
     qpat_assum `k + 32*(1+cap) <= sz` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_prov_def] >>
     rpt strip_tac >> goal_assum (drule_at Any) >> decide_tac) >>
  `w2n w+32*(1+cap) <= t'.vs_alloca_next /\ cap < dimword (:256)` by
    decide_tac >>
  `!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn1.t_mem` by
    metis_tac[] >>
  `cs_extends sa sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_def,
              compileEnvTheory.cs_extends_trans] >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid' t' /\
       storage_well_formed_on cx mid' (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t'` by
    (qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
  qpat_assum `~ctx_has_dalloca ctx`
    (fn th => irule (SRULE [th] append_nested_memory_cont_full)) >>
  simp[] >> conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`w`, `expr_type e`, `q`, `sm`, `lowered_value_type cenv e`, `vop`] >>
  simp[] >>
  reverse conj_tac >-
    (qpat_assum `ptr_covers G1 tn1 q t' _` mp_tac >>
     qpat_assum `place_ptr_rel cenv cx t' _ w _ _` mp_tac >>
     qpat_assum `loc = LocMemory` mp_tac >>
     qpat_assum `w = b + n2w k` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `compile_dynarray_append cenv r0 vop _ _ _ _ _ _ _ sm = _` mp_tac >>
  `type_memory_bytes cenv (expr_type e) = 32` by
    (qpat_assum `supported_full_word_type (expr_type e)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[supportedTypesTheory.supported_full_word_type_def] >>
     simp[compileEnvTheory.type_memory_bytes_def]) >>
  qpat_assum `type_memory_bytes cenv (expr_type e) = 32` mp_tac >>
  qpat_assum `r0 = Var q` mp_tac >>
  qpat_assum `loc = LocMemory` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[compileEnvTheory.word_scale_def, compileEnvTheory.elem_size_in_location_def,
       compileEnvTheory.is_slot_addressed_def]
QED

Resume append_nested_after_target_full[storage]:
  `t'' = ArrayTV tv (Dynamic cap)` by
    (qpat_assum `runtime_place_typed cx mid _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperTypeInvariantsTheory.runtime_place_typed_def,
          vyperStateTheory.place_type_value_def, return_def]) >>
  gvs[] >>
  drule vyperFiniteStoragePreservationTheory.eval_target_place_observed_region >>
  strip_tac >>
  `?xs. mid'.storage_trace = mid.storage_trace ++ xs` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (res,_)` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule_at Any vyperStorageTraceTheory.storage_trace_frame_prefix >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       storage_place_observed H (StoragePlace b c (ArrayTV tv (Dynamic cap)))` by
    (qpat_assum `MEM (StorageRoot _ _ _) mid.storage_trace` mp_tac >>
     qpat_assum `storage_subregion _ _ _ _` mp_tac >>
     qpat_assum `c = _` mp_tac >>
     qpat_assum `mid'.storage_trace = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[vyperStorageFootprintTheory.valid_horizon_def,
        vyperStorageFootprintTheory.storage_observations_ok_def,
        vyperStorageFootprintTheory.storage_trace_regions_def,
        listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     simp[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
     qexistsl_tac [`n2w offset`, `tv'`, `path`, `delta`] >> simp[] >>
     first_x_assum irule >>
     qexists_tac `[(b,n2w offset,tv')]` >> simp[] >>
     qexists_tac `StorageRoot b offset tv'` >> simp[]) >>
  `w = c /\ loc = slot_loc b` by
    (qpat_assum `place_ptr_rel cenv cx t' _ w _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[loweringPostsTheory.place_ptr_rel_def]) >>
  `op_taint tn1 r0 = {}` by
    (qpat_assum `target_ptr_ok _ _ _ G1 tn1 t'` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bodyFullTargetDefsTheory.target_ptr_ok_def]) >>
  `cap < dimword (:256)` by
    (qpat_assum `well_formed_type_value (ArrayTV _ _)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[vyperTypingTheory.well_formed_type_value_def]) >>
  `!l. r0 <> Label l` by
    (qpat_assum `target_pre cenv cx env bt es` mp_tac >>
     qpat_assum `type_place_target env bt = _` mp_tac >>
     qpat_assum `compile_get_target_ptr compile_expr cenv bt sa = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[targetPlaceSimTheory.target_pre_def] >> rpt strip_tac >>
     drule_all targetSubscriptSplitTheory.target_subscript_typed_base_not_label >> simp[]) >>
  `eval_operand r0 t' = SOME c` by
    (qpat_assum `eval_operand r0 t = SOME w` mp_tac >>
     qpat_assum `!x. r0 = Var x ==> _` mp_tac >>
     qpat_assum `!l. r0 <> Label l` mp_tac >>
     qpat_assum `!x w. not_fresh_at sp x /\ _ ==> _` mp_tac >>
     qpat_assum `w = c` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `r0` >> gvs[venomStateTheory.eval_operand_def]) >>
  `!x. r0 = Var x \/ shadow_op = Var x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `cs_extends sa sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_trans] >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid' t' /\
       storage_well_formed_on cx mid' (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t'` by
    (qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
  qpat_assum `~ctx_has_dalloca ctx`
    (fn th => irule (SRULE [th] append_nested_storage_cont_full)) >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`r0`, `expr_type e`, `sm`, `lowered_value_type cenv e`, `shadow_op`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  qpat_assum `compile_dynarray_append cenv r0 shadow_op _ _ _ _ _ _ _ sm = _` mp_tac >>
  `type_memory_bytes cenv (expr_type e) = 32` by
    (qpat_assum `supported_full_word_type (expr_type e)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[supportedTypesTheory.supported_full_word_type_def] >>
     simp[compileEnvTheory.type_memory_bytes_def]) >>
  qpat_assum `type_memory_bytes cenv (expr_type e) = 32` mp_tac >>
  qpat_assum `loc = slot_loc b` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `b` >>
  simp[loweringPostsTheory.slot_loc_def, compileEnvTheory.word_scale_def,
       compileEnvTheory.elem_size_in_location_def, compileEnvTheory.is_slot_addressed_def]
QED

Finalise append_nested_after_target_full[local]

(* A dynamic array reached through subscripts/attributes, rooted at a local
   (memory) or at a storage/transient/hashmap variable (gate SEQ-4806). *)
Theorem body_append_nested_full:
  !cx t e.
    (!id. t <> NameTarget id) /\ (!nid. t <> TopLevelNameTarget nid) /\
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t ==>
    body_stmt_full_ok cx (Append t e)
Proof
  rpt strip_tac >> rw[body_stmt_full_ok_def] >>
  rw[stmt_frag_full_def] >>
  `supported_full_word_type (expr_type e)` by
    (Cases_on `t` >> fs[supported_stmt_def]) >>
  `~(?nm. t = TopLevelNameTarget nm)` by metis_tac[] >>
  drule_all body_append_resolved_pre >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  simp[] >> strip_tac >>
  drule_all body_target_place_sim_full >>
  disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `shadow_ctx`, `func`,
    `shadow_func`] assume_tac) >>
  drule_all stmtSimAppendResolvedTheory.append_resolved_target_prefix >>
  strip_tac >> gvs[] >>
  rename1 `compile_get_target_ptr compile_expr cenv t sa = (r,sp)` >>
  `compile_get_target_ptr compile_expr cenv (gas_shadow_target t) shadow_sa =
      (r,SND (compile_get_target_ptr compile_expr cenv (gas_shadow_target t) shadow_sa)) /\
   gas_shadow_state sp
     (SND (compile_get_target_ptr compile_expr cenv (gas_shadow_target t) shadow_sa))` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `bt` |-> `t`]
       gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_get_target_ptr) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `compile_get_target_ptr compile_expr cenv (gas_shadow_target t) shadow_sa` >>
     simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_shadow_state sp shadow_sp` >>
  `ci_mono shadow_sa shadow_sp /\ ci_mono shadow_sp shadow_sb /\
   fn_has_code shadow_sa shadow_sp shadow_func /\
   fn_has_code shadow_sp shadow_sb shadow_func` by
    (qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     rewrite_tac[gasShadowTheory.gas_shadow_stmt_def] >> strip_tac >>
     drule_all stmtSimAppendResolvedTheory.append_resolved_target_prefix >>
     simp[] >> metis_tac[]) >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
    (rw[gasContextTheory.gas_admissible_def] >> Cases_on `res`
     >- simp[targetPlaceSimCasesTheory.target_place_res_ok_def] >>
     rename1 `eval_target_place cx t _ = (INR ex,ee)` >>
     `no_control_exc ex` by metis_tac[vyperExprNoControlTheory.eval_target_place_no_control] >>
     `eval_stmt cx (Append t e) (es with gas_obs := gs) = (INR ex,ee)` by
       simp[Once vyperInterpreterTheory.evaluate_def, bind_def] >>
     `stmt_res_ok lctx (INR ex)` by
       metis_tac[gasContextTheory.gas_admissible_def] >>
     gvs[stmtSimDefsTheory.stmt_res_ok_def, targetPlaceSimCasesTheory.target_place_res_ok_def,
         vyperExprNoControlTheory.no_control_exc_def]) >>
  qpat_x_assum `target_place_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyFullTargetDefsTheory.target_place_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `ArrayT (expr_type e) (Dynamic cap)`,
    `sa`, `sp`, `shadow_sa`, `shadow_sp`, `r`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[loweringPostsTheory.ret_pc_ok_def] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 R1` >>
  pure_once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result,
    vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_place] >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn u. Q1 H res ee G tn u /\ ~u.vs_halted` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "target_exit" >>
  simp[Abbr `Q1`] >> suspend "target_success"
QED

Resume body_append_nested_full[target_exit]:
  simp[Abbr `R1`] >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >> Cases_on `r'` >> gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def,
      exprSimDefsTheory.halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def]
QED

Resume body_append_nested_full[target_success]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  disj1_tac >> qexists_tac `p` >> simp[] >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE [])) >>
  `body_expr_full_ok cx e` by metis_tac[] >>
  `gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))
     (stmt_res_ok lctx) mid` by
    (rw[gasContextTheory.gas_admissible_def] >>
     qpat_assum `gas_admissible (eval_stmt _ _) _ _` mp_tac >>
     rewrite_tac[gasContextTheory.gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
     pure_once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
     pure_rewrite_tac[GSYM bind_assoc] >>
     simp[bind_def] >>
     qpat_x_assum `bind (bind _ _) _ _ = _` mp_tac >>
     pure_rewrite_tac[GSYM bind_assoc] >>
     simp[bind_def]) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `mid.gas_obs` (assume_tac o SRULE [])) >>
  pure_rewrite_tac [ETA_THM] >>
  `~ctx_has_dalloca ctx` by metis_tac[bodyInvNoDallocaTheory.body_inv_no_dalloca] >>
  simp[] >>
  qpat_assum `~ctx_has_dalloca ctx`
    (fn th => irule (SRULE [th] append_nested_after_target_full)) >>
  goal_assum (drule_at Any) >>
  simp[] >>
  conj_tac >- fs[loweringPostsTheory.ret_pc_ok_def] >>
  conj_tac >- (`cx_tops cx = tops` by fs[body_inv_def, gasContextTheory.cx_tops_def] >> simp[]) >>
  qexistsl_tac [`bindings`, `t`, `cap`, `env`, `es`,
    `gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs`, `r`, `ret_ty`,
    `shadow_func`, `shadow_sa`, `shadow_sb`, `shadow_sp`, `sp`] >>
  simp[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (qspec_then `H` mp_tac) >> gvs[]) >>
  conj_tac >- (fs[vyperTypeCallGraphTheory.int_calls_stmt_def] >>
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
      vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]) >>
  conj_tac >- (`cx_tops cx = tops` by fs[body_inv_def, gasContextTheory.cx_tops_def] >> simp[]) >>
  irule bodyMemoryDefsTheory.return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >>
  fs[ci_mono_def, loweringPostsTheory.target_post_def]
QED

Finalise body_append_nested_full
