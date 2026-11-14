(* Conditional nonlocal AugAssign producer: counted target prefix and loaded suffix. *)
Theory bodyIntCallFamStmtMutationAugPlaceProducer
Ancestors
  bodyIntCallFamStmtMutationAugPlacePrep
  bodyIntCallFamStmtMutationAugPlaceCompose
  bodyIntCallFamStmtMutationAugPlaceJoin
  bodyIntCallFamStmtMutationAugPlaceMemoryReady
  bodyIntCallFamStmtMutationAugPlaceStorageReady
  bodyAugAssignOther bodyIntCallJointStmtSeq
  bodyIntCallJointContract stmtSimAugAssignPlaceMemory
  supportedStmtTraverse vyperTypeCallGraph exprSimHypsDefs
  compileEnv stmtLoweringMono exprLoweringProps supportedStmts
  stmtSimAugAssignPlace vyperTypeSystem bodyExprPreFacts
  bodyAugPlaceTarget bodySim vyperTypeCallStackSoundness
  targetPlaceSim targetPlaceSimDefs supportedTargets fragExec

Theorem intcall_augassign_place_stmt_step:
  (!tg ce env es sa sb s vt op bindings.
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\ intcall_frame_ok fp /\
    body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    IS_SOME (supported_target_info fp.jc_tops bindings tg) /\
    target_pre ce fp.jc_cx env tg es /\ type_place_target env tg = SOME vt /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_target tg) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) tg ==>
       occurs_abi_decode_target target fp.jc_tops) /\
    compile_get_target_ptr compile_expr ce tg sa = (op,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    gas_admissible (eval_base_place fp.jc_cx tg) target_res_ok es /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_base_place fp.jc_cx tg) (es,s)
      (\res ee u. ?pv. res = INL pv /\
        target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee pv vt op u /\
        intcall_expr_cont fp ce env es sa s ee sb u)
      (\res ee r. expr_exit res r)) /\
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\ ~(?id. tg = NameTarget id) ==>
  intcall_stmts_producer fp [AugAssign ty tg bop rhs]
Proof
  strip_tac >>
  simp[intcall_stmts_producer_def,eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  `type_stmt env fp.jc_ret_ty (AugAssign ty tg bop rhs) = SOME env'` by
    gvs[vyperTypeSystemTheory.type_stmt_def,DISJ_IMP_THM,AllCaseEqs()] >>
  `supported_stmt fp.jc_tops bindings (AugAssign ty tg bop rhs)` by
    fs[supported_stmt_def] >>
  `stmt_exprs_ok ce (AugAssign ty tg bop rhs)` by fs[] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner
    (int_calls_stmt (AugAssign ty tg bop rhs))` by fs[] >>
  `!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (AugAssign ty tg bop rhs) ==> occurs_abi_decode_target target fp.jc_tops` by
    (fs[supported_stmts_expr_exists_list] >> metis_tac[]) >>
  drule aug_place_typing >> strip_tac >> gvs[] >>
  `body_stmt_safe fp.jc_tops (AugAssign ty tg bop rhs)` by
    metis_tac[supported_stmt_body_safe] >>
  `call_evaluation_safe fp.jc_cx (int_calls_stmt (AugAssign ty tg bop rhs))` by
    (fs[intcall_frame_ok_def,call_evaluation_safe_def] >> metis_tac[]) >>
  `expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `supported_expr fp.jc_tops rhs` by fs[supported_stmt_def] >>
  drule_all augassign_rhs_pre >> strip_tac >>
  drule_all bodyIntCallFamStmtMutationAugPlacePrepTheory.intcall_aug_place_entry_ready >>
  simp[] >> strip_tac >>
  `stmt_env ce lctx (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
     (AugAssign ty tg bop rhs) sa = (ce',sb)` by
    metis_tac[stmts_env_singleton] >>
  suspend "compound"
QED

Resume intcall_augassign_place_stmt_step[compound]:
  drule_all aug_place_code_parts >> strip_tac >>
  `cs_extends sa s0` by
    (qspecl_then [`tg`,`ce`,`sa`] mp_tac ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `cs_extends s0 sb` by
    (imp_res_tac aug_place_emit_void_grows >>
     imp_res_tac aug_place_emit_op_grows >>
     imp_res_tac (cj 2 compile_expr_grows) >>
     imp_res_tac compile_binop_grows >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s0 fp.jc_func` by
    metis_tac[fn_has_code_mid,cs_extends_refl] >>
  `gas_admissible (eval_base_place fp.jc_cx tg) target_res_ok es` by
    metis_tac[aug_place_base_admissible] >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_target tg)` by
    fs[int_calls_stmt_def] >>
  `!target. supported_target_exists (expr_abi_decode_target_root target) tg ==>
     occurs_abi_decode_target target fp.jc_tops` by
    (fs[supported_stmt_expr_exists_def] >> metis_tac[]) >>
  `IS_SOME (supported_target_info fp.jc_tops bindings tg)` by simp[] >>
  qpat_x_assum `!tg' ce'' env'' es' sa' sb' s'' vt op bindings'. _`
    (qspec_then `tg` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  suspend "target_outcome"
QED

Resume intcall_augassign_place_stmt_step[target_outcome]:
  markerLib.RESUME_TAC >>
  (Cases_on `FST (SND r) = NONE` >- suspend "invalid") >>
  `!id path gs mid. eval_target_place fp.jc_cx tg (es with gas_obs := gs) =
      (INL (MemoryPlace id path),mid) ==>
      ((?bt fld. tg = AttributeTarget bt fld) \/
       (?bt key. tg = SubscriptTarget bt key))` by
    (Cases_on `tg` >> gvs[] >> rpt strip_tac >>
     drule_at (Pat `eval_target_place`)
       stmtSimAugAssignPlaceStorageTheory.aug_place_supported_storage_kind >>
     simp[target_root_def] >> metis_tac[]) >>
  drule_at (Pat `gas_outcome`) intcall_aug_place_prepared_outcome >>
  disch_then (drule_at (Pat `stmt_env`)) >>
  disch_then (drule_at (Pat `type_stmt`)) >>
  disch_then (drule_at (Pat `supported_target_info`)) >>
  (impl_tac >- (fs[body_inv_def,int_calls_stmt_def] >> metis_tac[])) >>
  strip_tac >>
  irule exprSimSubscriptMapTheory.gas_outcome_conseq >>
  goal_assum (drule_at (Pat `gas_outcome`)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  simp[loweringPostsTheory.stmt_lands_def,stmtSimPropsTheory.cenv_top_ext_refl] >>
  gvs[] >>
  drule exprOpenPrimitivesTheory.emit_void_terminated >>
  Cases_on `loc` >> simp[venomInstTheory.is_terminator_def]
QED

Resume intcall_augassign_place_stmt_step[invalid]:
  markerLib.RESUME_TAC >> gvs[] >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  simp[Once vyperInterpreterTheory.evaluate_def,vyperStateTheory.bind_assoc] >>
  irule exprSimSubscriptMapTheory.gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome`)) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      fs[exprSimDefsTheory.expr_exit_def,intcall_stmt_exit_def] >>
      disj1_tac >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[loweringPostsTheory.target_post_def] >>
  Cases_on `v` >> gvs[loweringPostsTheory.place_ptr_rel_def] >>
  Cases_on `p` >> gvs[loweringPostsTheory.place_ptr_rel_def]
QED

Finalise intcall_augassign_place_stmt_step
