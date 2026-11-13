Theory bodyPtrAugAssignPureStorage
Ancestors
  augAssignPtrStorageSuffix augAssignPtrStorageCompose augAssignPtrStorageTargetReady
  bodyPtrAugAssignLocalPrefix bodyPtrPreds bodyPtrDefs bodyAugAssignOther
  bodyAugPlaceTarget stmtSimAugAssignPlaceStorage stmtSimAugAssignPlace
  bodySimAugPlaceLive bodySimAugPlaceScopes bodyExprPreFacts
  bodySim exprSimHypsDefs exprSimSource exprSimProps exprSimDefs
  supportedStmts supportedStmtTraverse supportedExprTraverse allocLimits
  stmtLoweringMono stmtLowering exprLoweringProps compileEnv
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState vyperAST loweringPosts targetPlaceSim
  gasContext gasSummaryComposePtr fragGasPathPtr fragExec bodyPtrPopTargetDefs
  freshWrites finite_map list bodyPtrPopTargetSimCoverage ptrDiscipline
  targetPlaceSimCasesBase supportedTargets targetPlaceLive
  augAssignPtrMemoryOutcome augAssignPtrMemoryCompose emitHelperProps exprBopSimProps
  stmtSimAugAssignPlaceMemory bodyPtrPopSeamTargetSim

(* The posts here keep the source state as `es_end with gas_obs := []`;
   stripping gas_obs only inside target_post would split it from expr_post. *)
val _ = temp_delsimps ["tuple_place_target_post_gas_obs"];

Theorem body_augassign_pure_storage_place_ptr:
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
    (!id. target_root t <> NameTarget id) ==>
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
     irule stmt_expr_body_pre >> fs[body_inv_def, cx_tops_def] >>
     metis_tac[call_evaluation_safe_append_right, APPEND_NIL]) >>
  `?info. supported_target_info tops bindings t = SOME info` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  `target_indices_pre cenv cx env t` by metis_tac[augassign_target_pre] >>
  `~immutable_root cx t` by metis_tac[aug_place_supported_root_not_immutable] >>
  `target_pre cenv cx env t es` by
    (fs[target_pre_def] >> metis_tac[aug_place_typing]) >>
  `target_sim_ptr d ctx PG func cenv cx env t es` by
    (irule body_target_sim_ptr >> simp[] >> metis_tac[]) >>
  `!sa r sb. compile_get_target_ptr compile_expr cenv t sa = (r,sb) ==>
      !l. FST r <> Label l` by metis_tac[aug_place_target_ptr_not_label] >>
  qpat_x_assum `(?b fld. _) \/ (?b k. _)` kall_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  drule_all aug_place_code_parts >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `r` (qx_choose_then `sm` strip_assume_tac))) >>
  `cs_extends sa sm` by
    (qspecl_then [`compile_expr`, `t`, `cenv`, `sa`]
      mp_tac ci_mono_compile_get_target_ptr_cfn >>
     simp[cj 1 compile_expr_ci_mono, ci_mono_def] >> rpt strip_tac >> gvs[]) >>
  `cs_extends sm sb` by
    (imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
     imp_res_tac (CONJUNCT2 compile_expr_grows) >> imp_res_tac compile_binop_grows >>
     fs[cs_appends_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `gas_admissible (eval_base_place cx t) target_res_ok es` by
    metis_tac[aug_place_base_admissible] >>
  qpat_x_assum `target_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[target_sim_ptr_def] >>
  disch_then (qspecl_then [`Type ty`, `sa`, `sm`, `r`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- fs[ret_pc_ok_def]) >> strip_tac >>
  (qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
   >- suspend "target_summary" >>
   drule augassign_base_exempt_outcome_ptr >> simp[])
QED

Resume body_augassign_pure_storage_place_ptr[target_summary]:
  markerLib.RESUME_TAC >>
  (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
   simp[gas_summary_ptr_at_marked] >> strip_tac
   >- suspend "target_normal" >>
   `?exc. res = INR exc` by (Cases_on `res` >> gvs[expr_exit_def]) >>
   gvs[] >> irule augassign_base_exit_outcome_ptr >>
   goal_assum (drule_at Any) >> simp[stmt_exit_ptr_def] >>
   metis_tac[stmtSimPropsTheory.expr_exit_INR_type])
QED

Resume body_augassign_pure_storage_place_ptr[target_normal]:
  markerLib.RESUME_TAC >> gvs[] >>
  (Cases_on `FST (SND r) = NONE`
   >- (fs[target_post_def] >> Cases_on `pv` >>
       fs[place_ptr_rel_def] >> rename1 `PlaceR p` >>
       Cases_on `p` >> fs[place_ptr_rel_def])) >> gvs[] >>
  qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `target_pre cenv cx env t
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by
    fs[target_pre_def] >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by
    fs[expr_body_pre_def] >>
  `target_post ctx func cenv cx
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])
     sa sm s0 (es_end with gas_obs := []) pv (Type ty) r t'` by
    (qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[target_post_def, locals_kept_def, popped_kept_def] >>
     metis_tac[]) >>
  drule_all aug_place_storage_target_ready_ptr >> strip_tac >> gvs[] >>
  `body_expr_ptr_ok cx e` by metis_tac[] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `0 < type_slot_size tv` by
    (irule assignable_type_slot_size_pos >>
     fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[]) >>
  `emit_op (if tr then TLOAD else SLOAD) [FST r] sm = (cur,s1) /\
   emit_void (if tr then TSTORE else SSTORE) [FST r;result] s3 = ((),sb)` by
    (Cases_on `tr` >> fs[slot_loc_def]) >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
  `cs_extends s1 sb` by
    (imp_res_tac (CONJUNCT2 compile_expr_grows) >>
     imp_res_tac compile_binop_grows >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code sm s1 func` by
    (irule fn_has_code_mid >> conj_tac >- simp[] >>
     qexistsl_tac [`sb`,`sa`] >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`t`,`cenv`,`sa`] mp_tac
       stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `ret_pc_ok cenv sm t'` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >> fs[target_post_def] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `~t'.vs_halted` by metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted] >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  qpat_x_assum `cur = Var _` SUBST_ALL_TAC >>
  drule_all aug_place_storage_ready_load_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3` by
    (imp_res_tac (CONJUNCT2 compile_expr_grows) >>
     imp_res_tac compile_binop_grows >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    (rpt conj_tac >> irule fn_has_code_mid >>
     metis_tac[cs_extends_trans,cs_extends_refl]) >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[] >> decide_tac) >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z` by
    (fs[ret_pc_ok_def] >> metis_tac[not_fresh_at_mono]) >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z` by
    metis_tac[not_fresh_at_mono] >>
  `well_formed_type env.type_defs ty` by metis_tac[assignable_type_well_formed] >>
  `word_value cur'` by metis_tac[word_value_type_typed] >>
  `eval_operand (Var tmp) u = SOME (val_to_w256 cur')` by
    metis_tac[typed_val_to_w256_word_value] >>
  `!l. FST r <> Label l` by metis_tac[] >>
  `eval_operand (FST r) u = SOME slot` by
    (irule eval_operand_frame >> conj_tac
     >- simp[] >>
     qexistsl_tac [`sm`,`t'`] >> simp[]) >>
  `!l. Var tmp <> Label l /\ FST r <> Label l` by simp[] >>
  `!z. FST r = Var z ==> not_fresh_at s1 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `op_taint tm (FST r) = {}` by
    (Cases_on `FST r` >> fs[ghost_kept_def, op_taint_def]) >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
     lookup_var z u = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sm z` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     `lookup_var z u = lookup_var z t'` by simp[] >>
     fs[target_post_def] >> metis_tac[]) >>
  `!z. not_fresh_at sa z ==> FLOOKUP H z = FLOOKUP G0 z /\
       op_taint tm (Var z) = op_taint tn0 (Var z)` by
    (rpt strip_tac >>
     `not_fresh_at sm z` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     fs[ghost_kept_def]) >>
  `!w st. storage_dead cx tr (update_storage slot w st) = storage_dead cx tr st` by
    (irule aug_place_target_storage_dead_stable >>
     goal_assum (drule_at Any) >>
     metis_tac[exprSimUnwrapTheory.word_type_slot_size]) >>
  `gas_admissible
    (bind (bind (eval_expr cx e) (read_result cx)) (\v.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur' v)) (write_storage_slot cx tr slot tv)))
    (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (assume_tac o MATCH_MP gas_marked_exec_ptr_exec) >>
     qpat_x_assum `gas_admissible (eval_stmt _ _) _ _` mp_tac >>
     rewrite_tac[Once evaluate_def, aug_place_target_bind_base, bind_assoc] >>
     disch_then (mp_then Any mp_tac aug_place_marked_bind_tail) >>
     disch_then drule >>
     simp[get_place_def, bind_return, place_type_value_def] >>
     `!gs. read_storage_slot cx tr slot tv (es_end with gas_obs := gs) =
       (INL cur', es_end with gas_obs := gs)` by
       (gen_tac >>
        qpat_assum `read_place _ _ _ = _` mp_tac >>
        pure_rewrite_tac[read_place_def] >>
        strip_tac >>
        drule augAssignPtrStorageCommonTheory.read_storage_slot_gas_obs_ptr >>
        disch_then (qspec_then `gs` mp_tac) >> simp[]) >>
     simp[gas_admissible_def, bind_def, read_place_def, write_place_def]) >>
  mp_tac (Q.INST [`s0` |-> `u`, `G0` |-> `H`, `tn0` |-> `tm`,
    `es` |-> `es_end with gas_obs := []`, `t` |-> `u`,
    `cur` |-> `Var tmp`,
    `dst` |-> `FST (r : operand # data_location option # place_ty option)`,
    `op` |-> `result`, `tvt` |-> `tv`, `v` |-> `cur'`] augassign_storage_rhs_suffix_ptr) >>
  (impl_tac >- (simp[ghost_kept_def, expr_body_pre_def] >> metis_tac[])) >>
  strip_tac >>
  simp[Once evaluate_def] >>
  ho_match_mp_tac (GEN_ALL aug_place_storage_outer_place_outcome_ptr) >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_place _ _ _ = _`)) >>
  simp[GSYM bind_assoc, write_place_def, ETA_AX] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (assume_tac o SIMP_RULE (srw_ss()) [GSYM bind_assoc]) >>
  pure_rewrite_tac[GSYM bind_assoc, ETA_AX] >>
  irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qexists_tac `cenv'` >> simp[] >> metis_tac[]
QED

Finalise body_augassign_pure_storage_place_ptr
