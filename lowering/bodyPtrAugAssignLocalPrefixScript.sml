Theory bodyPtrAugAssignLocalPrefix
Ancestors
  augAssignPtrMemoryOutcome augAssignPtrMemoryLoad augAssignPtrMemoryCompose
  bodyPtrPopSeamTargetSim bodyPtrPreds bodyPtrDefs bodyAugAssignOther
  bodyAugPlaceTarget stmtSimAugAssignPlaceMemory stmtSimAugAssignPlace
  bodySimAugPlaceLive bodySimAugPlaceScopes bodyExprPreFacts
  bodySim exprSimHypsDefs exprSimSource exprSimProps exprSimDefs
  supportedStmts supportedStmtTraverse supportedExprTraverse allocLimits
  stmtLoweringMono stmtLowering exprLoweringProps compileEnv
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState vyperAST loweringPosts targetPlaceSim
  gasContext gasSummaryComposePtr fragGasPathPtr fragExec bodyPtrPopTargetDefs
  freshWrites finite_map list bodyPtrWordBuiltinsObservedOutcome bodyPtrBopTypedSource
  bodyPtrPopStoragePureFrame bodyPtrEnvBuiltinsGhostCompose
  vyperEvalExprPreservesScopesDom

(* The posts here keep the source state as `es_end with gas_obs := []`;
   stripping gas_obs only inside target_post would split it from expr_post. *)
val _ = temp_delsimps ["tuple_place_target_post_gas_obs"];

Theorem body_augassign_local_place_from_suffix_ptr:
  !d PG cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s0 p s1 s2 cur s3 s4 ptv s5.
       eval_target_place cx t s0 = (INL p,s1) /\
       read_place cx p s2 = (INL cur,s3) /\
       place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ptr_ok cx e) /\
    body_base_target_ptr_ok cx t /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    body_stmt_safe tops (AugAssign ty t bop e) /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) /\
    ((?b fld. t = AttributeTarget b fld) \/ (?b k. t = SubscriptTarget b k)) /\
    (?id. target_root t = NameTarget id) /\
    (!id. target_root t = NameTarget id ==> local_target_live cx id t) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `supported_expr tops e` by fs[supported_stmt_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule supported_expr_body_calls >> strip_tac >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         int_calls_stmt_def, AllCaseEqs()] >>
     irule stmt_expr_body_pre >>
     fs[body_inv_def, cx_tops_def] >>
     metis_tac[call_evaluation_safe_append_right, APPEND_NIL]) >>
  `?info. supported_target_info tops bindings t = SOME info` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  `target_indices_pre cenv cx env t` by metis_tac[augassign_target_pre] >>
  `~immutable_root cx t` by
    metis_tac[aug_place_supported_root_not_immutable] >>
  `target_pre cenv cx env t es` by
    (fs[target_pre_def] >> metis_tac[aug_place_typing]) >>
  `target_sim_ptr d ctx PG func cenv cx env t es` by
    (irule body_target_sim_ptr >> simp[] >>
     metis_tac[vyperASTTheory.base_assignment_target_distinct]) >>
  qpat_x_assum `(?b fld. _) \/ (?b k. _)` kall_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  drule_all aug_place_code_parts >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `r` (qx_choose_then `sm` strip_assume_tac))) >>
  `cs_extends sa sm` by
    (qspecl_then [`compile_expr`, `t`, `cenv`, `sa`]
      mp_tac ci_mono_compile_get_target_ptr_cfn >>
     simp[cj 1 compile_expr_ci_mono, ci_mono_def] >>
     rpt strip_tac >> gvs[]) >>
  `cs_extends sm sb` by
    (imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
     imp_res_tac (CONJUNCT2 compile_expr_grows) >>
     imp_res_tac compile_binop_grows >>
     fs[cs_appends_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `gas_admissible (eval_base_place cx t) target_res_ok es` by
    metis_tac[aug_place_base_admissible] >>
  qpat_x_assum `target_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[target_sim_ptr_def] >>
  disch_then (qspecl_then [`Type ty`, `sa`, `sm`, `r`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- fs[ret_pc_ok_def]) >>
  strip_tac >>
  (qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
   >- suspend "target_summary" >>
   drule augassign_base_exempt_outcome_ptr >> simp[])
QED

Resume body_augassign_local_place_from_suffix_ptr[target_summary]:
  markerLib.RESUME_TAC >>
  (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
   simp[gas_summary_ptr_at_marked] >> strip_tac
   >- suspend "target_normal" >>
   `?exc. res = INR exc` by (Cases_on `res` >> gvs[expr_exit_def]) >>
   gvs[] >> irule augassign_base_exit_outcome_ptr >>
   goal_assum (drule_at Any) >>
   simp[stmt_exit_ptr_def] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type])
QED

Resume body_augassign_local_place_from_suffix_ptr[target_normal]:
  markerLib.RESUME_TAC >> gvs[] >>
  (Cases_on `FST (SND r) = NONE`
   >- (fs[target_post_def] >> Cases_on `pv` >>
       fs[place_ptr_rel_def] >> rename1 `PlaceR p` >>
       Cases_on `p` >> fs[place_ptr_rel_def])) >> gvs[] >>
  `?path. pv = PlaceR (MemoryPlace id path)` by
    (qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     metis_tac[aug_place_name_root_base]) >> gvs[] >>
  `!tail. eval_target_place cx t
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (MemoryPlace id path), es_end with gas_obs := tail)` by
    (qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
     simp[Once evaluate_def, bind_def, get_place_def, return_def]) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[target_post_def, place_readable_def] >> strip_tac >>
  `loc = LocMemory` by
    (fs[place_ptr_rel_def] >> metis_tac[optionTheory.SOME_11]) >> gvs[] >>
  `expr_body_pre cenv cx env e (es_end with gas_obs := [])` by
    (irule aug_place_rhs_pre_target_gas_obs >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  drule_all aug_place_target_memory_live >> strip_tac >>
  `expr_sim_inv cenv cx env (es_end with gas_obs := [])` by
    fs[expr_body_pre_def] >>
  `?ptv. evaluate_type (get_tenv cx) ty = SOME ptv /\
     place_type_value cx (MemoryPlace id path) (es_end with gas_obs := []) =
       (INL ptv,es_end with gas_obs := [])` by
    (irule aug_place_memory_type_read >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `body_expr_ptr_ok cx e` by metis_tac[] >>
  `place_readable cx (es_end with gas_obs := [])
     (PlaceR (MemoryPlace id path))` by
    (rewrite_tac[place_readable_def] >> qexists_tac `v` >> asm_rewrite_tac[]) >>
  drule_all bodyPtrPopTargetSimIndexSourceTheory.target_readable_local_type_ptr >>
  strip_tac >>
  `!entry. lookup_scopes id (es_end with gas_obs := []).scopes = SOME entry ==>
      ISL (evaluate_subscripts entry.type entry.value path)` by
    (rpt strip_tac >> gvs[]) >>
  PairCases_on `r` >> gvs[] >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
  `cs_extends s1 sb` by
    (imp_res_tac (CONJUNCT2 compile_expr_grows) >>
     imp_res_tac compile_binop_grows >>
     imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
     irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `fn_has_code sm s1 func` by
    (irule fn_has_code_mid >> conj_tac >- simp[] >>
     qexistsl_tac [`sb`, `sa`] >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >>
     qspecl_then [`t`, `cenv`, `sa`] mp_tac
       stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`t`, `cenv`, `sa`] mp_tac
       stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `ret_pc_ok cenv sm t'` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >>
     metis_tac[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `~t'.vs_halted` by
    (qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[gas_marked_exec_ptr_def] >> rpt strip_tac >>
     drule fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted >> simp[]) >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  qpat_x_assum `cur = Var _` SUBST_ALL_TAC >>
  `s1.cs_current_bb = sm.cs_current_bb` by metis_tac[] >>
  drule augassign_memory_load_clean_frame_ptr >>
  disch_then (drule_at Any) >> simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `expr_body_pre cenv cx env e (es_end with gas_obs := [])` by
    fs[expr_body_pre_gas_obs] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx))
     expr_res_ok (es_end with gas_obs := [])` by
    (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  `fn_has_code s1 s2 func` by
    (imp_res_tac (CONJUNCT2 compile_expr_grows) >>
     irule fn_has_code_mid >> conj_tac >- simp[] >>
     qexistsl_tac [`sb`, `sa`] >> simp[] >> conj_tac
     >- (irule cs_extends_trans >> qexists_tac `s3` >>
         imp_res_tac compile_binop_grows >> simp[]) >>
     irule cs_extends_trans >> qexists_tac `sm` >> simp[]) >>
  `expr_sim_ptr d ctx PG func cenv cx ty e (es_end with gas_obs := [])` by
    (qpat_assum `body_expr_ptr_ok cx e` mp_tac >>
     qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env e (es_end with gas_obs := [])` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[body_expr_ptr_ok_def] >> metis_tac[expr_body_pre_gas_obs]) >>
  `ret_pc_ok cenv s1 t''` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >>
     qexistsl_tac [`cenv`, `t'`, `sm`] >> simp[] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at s1 x` by
    (qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at sm x` mp_tac >>
     qpat_assum `emit_op MLOAD _ sm = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     metis_tac[not_fresh_at_mono, arithmeticTheory.LE_ADD]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs`, `t''`, `H`, `tm`] mp_tac) >>
  (impl_tac >- fs[ret_pc_ok_def]) >>
  strip_tac >>
  drule gas_outcome_ptr_observed_path_strengthen >>
  disch_then (qspec_then `\res ee G tn s. ~s.vs_halted /\ ?obs. !tail.
    bind (eval_expr cx e) (read_result cx)
      (es_end with gas_obs := obs ++ tail) = (res, ee with gas_obs := tail)` mp_tac) >>
  (impl_tac >-
    (rpt strip_tac >>
     qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def] >> strip_tac >>
     conj_tac >- metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted] >>
     goal_assum (drule_at Any))) >>
  strip_tac >>
  irule augassign_memory_rhs_outcome_ptr >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_place _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `place_type_value _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  simp[] >> suspend "rhs_continuations"
QED

Resume body_augassign_local_place_from_suffix_ptr[rhs_continuations]:
  markerLib.RESUME_TAC >> conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- gvs[expr_exit_def] >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[stmt_exit_ptr_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
      (es_end with gas_obs := obs) = (INL v'', ee with gas_obs := [])` by
    (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `[]` mp_tac) >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e (es_end with gas_obs := obs)` by
    fs[expr_body_pre_gas_obs] >>
  `expr_sim_inv cenv cx env (ee with gas_obs := []) /\
   ?rtv. word_value v'' /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME rtv /\
     value_has_type rtv v''` by
    (qpat_x_assum `expr_body_pre cenv cx env e (es_end with gas_obs := obs)` mp_tac >>
     qpat_x_assum `bind _ _ (es_end with gas_obs := obs) = _` mp_tac >>
     qpat_x_assum `word_value_type (expr_type e)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[expr_body_pre_word_result, ETA_THM]) >>
  `ee.scopes = es_end.scopes` by
    (qpat_x_assum `bind _ _ (es_end with gas_obs := obs) = _` mp_tac >>
     qpat_x_assum `supported_expr tops e` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[bind_def, AllCaseEqs()] >>
     imp_res_tac aug_place_supported_expr_scopes >>
     imp_res_tac read_result_state >> gvs[]) >>
  `expr_sim_inv cenv cx env ee` by
    fs[expr_sim_inv_gas_obs] >>
  `lookup_scopes id ee.scopes = SOME entry /\
   evaluate_subscripts entry.type entry.value path = INL v'` by simp[] >>
  `!gs. read_place cx (MemoryPlace id path) (es_end with gas_obs := gs) =
      (INL v,es_end with gas_obs := gs)` by
    (gen_tac >> qpat_assum `read_place _ _ (es_end with gas_obs := []) = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     strip_tac >>
     qspecl_then [`cx`, `MemoryPlace id path`, `es_end with gas_obs := []`, `gs`]
       mp_tac exprSimLenTheory.len_rp_obs >> simp[]) >>
  `!gs. place_type_value cx (MemoryPlace id path) (es_end with gas_obs := gs) =
      (INL ptv,es_end with gas_obs := gs)` by
    (qpat_x_assum `place_type_value _ _ (es_end with gas_obs := []) = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     Cases_on `lookup_scopes id es_end.scopes` >>
     gvs[place_type_value_def, get_scopes_def, bind_def, return_def,
         lift_option_type_def, raise_def] >>
     Cases_on `subscripts_type x.type path` >> gvs[return_def, raise_def]) >>
  `!gs. eval_stmt cx (AugAssign ty t bop e)
      (es with gas_obs := (gas_explicit marks s0.vs_gas_readings ++ obs) ++ gs) =
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop v v'')) (write_place cx (MemoryPlace id path))
          (ee with gas_obs := gs)` by
    (gen_tac >> pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[Once evaluate_def, bind_def, Excl "APPEND_ASSOC"] >>
     qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _` (qspec_then `gs` mp_tac) >>
     Cases_on `eval_expr cx e (es_end with gas_obs := obs ++ gs)` >>
     Cases_on `q` >>
     pure_asm_rewrite_tac[bind_def] >>
     Cases_on `read_result cx x r` >> gvs[]) >>
  `gas_admissible
      (bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop v v'')) (write_place cx (MemoryPlace id path)))
      (stmt_res_ok lctx) ee` by
    (qpat_x_assum `gas_admissible (eval_stmt cx _) _ _` mp_tac >>
     qpat_x_assum `!gs. eval_stmt cx _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[gas_admissible_def] >>
     rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `type_bits ty MOD 8 = 0` by
    (irule stmtSimAugAssignTheory.well_formed_type_bits >>
     qexists_tac `get_tenv cx` >> simp[well_formed_type_def] >> metis_tac[]) >>
  drule_all aug_place_rhs_suffix_ready >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  `(!n. expr_int_literal e = SOME n ==> v'' = IntV n) /\
   (shift_amount_ok e ==> ?i. v'' = IntV i /\ 0 <= i)` by
    (`expr_body_pre cenv cx env e (es_end with gas_obs := obs)` by
       fs[expr_body_pre_gas_obs] >>
     qpat_x_assum `expr_body_pre cenv cx env e (es_end with gas_obs := obs)` mp_tac >>
     qpat_x_assum `bind _ _ (es_end with gas_obs := obs) = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `?gs. bind (eval_expr cx e) (read_result cx)
        ((es_end with gas_obs := obs) with gas_obs := gs) =
        (INL v'', ee with gas_obs := [])` by
       (qexists_tac `obs` >> simp[]) >>
     metis_tac[bop_typed_source_witness]) >>
  `(bop = Exp ==> (?n. expr_int_literal e = SOME n /\ 0 <= n) /\
       (!n. expr_int_literal e = SOME n ==> v'' = IntV n)) /\
   (bop = ShL \/ bop = ShR ==> ?i. v'' = IntV i /\ 0 <= i)` by
    (qpat_x_assum `bop = Exp ==> nonneg_int_literal e` mp_tac >>
     qpat_x_assum `bop = ShL \/ bop = ShR ==> shift_amount_ok e` mp_tac >>
     qpat_x_assum `!n. expr_int_literal e = SOME n ==> v'' = IntV n` mp_tac >>
     qpat_x_assum `shift_amount_ok e ==> ?i. v'' = IntV i /\ 0 <= i` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `expr_int_literal e` >>
     simp[nonneg_int_literal_def, GSYM exprSimHypsTheory.expr_int_literal_value] >>
     rpt strip_tac >> gvs[]) >>
  `is_word_type (expr_type e)` by metis_tac[word_value_type_word] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `op_prov G' rhs = NONE /\ op_taint tn' rhs = {}` by
    (fs[ptr_val_ok_def, post_value_type_word]) >>
  `eval_operand rhs s = SOME (val_to_w256 v'')` by
    (fs[expr_post_def, post_value_type_word, expr_val_rel_def] >>
     metis_tac[exprSimPropsTheory.typed_val_to_w256_word_value]) >>
  qmatch_asmsub_abbrev_tac `lookup_var saved t'' = SOME _` >>
  `eval_operand (Var saved) s = SOME (val_to_w256 v)` by
    (simp[venomStateTheory.eval_operand_def] >>
     `typed_val_to_w256 ptv v = val_to_w256 v` by
       (qpat_x_assum `word_value_type ty` mp_tac >>
        qpat_x_assum `evaluate_type (get_tenv cx) ty = SOME ptv` mp_tac >>
        qpat_x_assum `value_has_type ptv v` mp_tac >>
        rpt (pop_assum kall_tac) >>
        metis_tac[word_value_type_typed,
          exprSimPropsTheory.typed_val_to_w256_word_value]) >>
     fs[expr_post_def] >>
     qpat_x_assum `!x w. not_fresh_at s1 x /\ lookup_var x t'' = SOME w ==> _`
       (qspecl_then [`saved`, `val_to_w256 v`] mp_tac) >> simp[]) >>
  `op_prov G' (Var saved) = NONE /\ op_taint tn' (Var saved) = {}` by
    (fs[ghost_kept_def, ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  drule target_memory_word_inputs_ptr >>
  simp[expr_sim_inv_gas_obs] >> disch_then drule_all >> strip_tac >> gvs[] >>
  rename1 `lookup_var dst t' = SOME addr` >>
  `not_fresh_at s1 dst` by
    (irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> simp[] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `lookup_var dst s = SOME addr` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `lookup_var dst t'' = SOME addr` by metis_tac[] >>
  `ptr_covers H tm dst t'' 32` by
    (qpat_x_assum `ghost_kept _ _ sm G tn t' H tm` mp_tac >>
     qpat_x_assum `ptr_covers G tn dst t' 32` mp_tac >>
     qpat_x_assum `not_fresh_at sm dst` mp_tac >>
     qpat_x_assum `lookup_var dst t' = SOME addr` mp_tac >>
     qpat_x_assum `lookup_var dst t'' = SOME addr` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[bodyPtrIfExpAllocProbeTheory.ptr_covers_ghost_kept]) >>
  `ptr_covers G' tn' dst s 32` by
    (qpat_x_assum `ghost_kept _ _ s1 H tm t'' G' tn'` mp_tac >>
     qpat_x_assum `ptr_covers H tm dst t'' 32` mp_tac >>
     qpat_x_assum `not_fresh_at s1 dst` mp_tac >>
     qpat_x_assum `lookup_var dst t'' = SOME addr` mp_tac >>
     qpat_x_assum `lookup_var dst s = SOME addr` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[bodyPtrIfExpAllocProbeTheory.ptr_covers_ghost_kept]) >>
  `!z w. not_fresh_at sm z /\ lookup_var z t' = SOME w ==>
      lookup_var z s = SOME w` by
    (fs[expr_post_def] >> rpt strip_tac >>
     `not_fresh_at s1 z` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
        simp[] >> drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
     metis_tac[]) >>
  `place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) addr
      (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >>
     qexistsl_tac [`t'`, `sm`] >>
     fs[venomStateTheory.eval_operand_def]) >>
  `sm.cs_next_var <= s1.cs_next_var` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `s2.cs_next_var <= s3.cs_next_var /\ cs_extends s2 s3` by
    metis_tac[compile_binop_grows] >>
  `!z. not_fresh_at sa z ==> not_fresh_at s2 z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> decide_tac) >>
  `!z. not_fresh_at s2 z ==> not_fresh_at s3 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `not_fresh_at s2 saved /\ not_fresh_at s2 dst` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s1` >> simp[]) >>
  `fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    (conj_tac
     >- (irule fn_has_code_mid >> conj_tac >- simp[] >>
         qexistsl_tac [`sb`, `sa`] >> simp[] >>
         irule cs_extends_trans >> qexists_tac `s1` >> simp[] >>
         irule cs_extends_trans >> qexists_tac `sm` >> simp[]) >>
     irule fn_has_code_mid >> conj_tac >- simp[] >>
     qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl] >>
     irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s1` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `sm` >> simp[]) >>
  `ci_mono sa sm` by
    (qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     metis_tac[pairTheory.SND]) >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_assum `!tail. eval_target_place cx t _ = _`
       (qspec_then `[]` mp_tac) >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule eval_target_place_preserves_scopes_dom >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes s0` by fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `ghost_kept cenv es sa G0 tn0 s0 H tm` by
    (irule target_post_ghost_kept_compose >> conj_tac >- simp[] >>
     qexists_tac `G` >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists_tac `tn` >> simp[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule bodyPtrEnvBuiltinsGhostComposeTheory.ghost_kept_locals_trans >>
     simp[] >> conj_tac >- (qexists_tac `func` >> simp[]) >>
     qexists_tac `H` >>
     qpat_assum `ghost_kept _ _ s1 H tm t'' G' tn'` (irule_at Any) >>
     simp[] >>
     `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
       metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >>
     fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  irule augassign_memory_binop_write_outcome_ptr >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists_tac `lctx` >> simp[]) >>
  qpat_assum `compile_binop _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >>
  qpat_assum `ghost_kept cenv es sa G0 tn0 s0 G' tn'` (irule_at Any) >>
  qpat_assum `expr_sim_inv cenv cx env ee` (irule_at Any) >>
  qpat_assum `ghost_inv d cenv cx ee G' tn' s` (irule_at Any) >>
  qpat_assum `evaluate_type _ (expr_type e) = SOME _` (irule_at Any) >>
  qexists_tac `addr` >> simp[] >>
  conj_tac >-
    (qpat_assum `!z w. not_fresh_at sm z /\ _ ==> lookup_var z s = _` mp_tac >>
     qpat_assum `!x w. not_fresh_at sa x /\ _ ==> lookup_var x t' = _` mp_tac >>
     qpat_assum `ci_mono sa sm` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  conj_tac >-
    (qpat_assum `ret_pc_ok cenv sa s0` mp_tac >>
     qpat_assum `!z. not_fresh_at sa z ==> not_fresh_at s2 z` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ret_pc_ok_def] >> metis_tac[]) >>
  reverse conj_tac >- fs[expr_post_def] >>
  rpt strip_tac >>
  simp[stmt_lands_def, stmtSimPropsTheory.cenv_top_ext_refl,
       stmtFragPtrTheory.ghost_inv_gas_obs] >>
  drule exprOpenPrimitivesTheory.emit_void_terminated >>
  simp[venomInstTheory.is_terminator_def]
QED

Finalise body_augassign_local_place_from_suffix_ptr
