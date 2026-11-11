(* Expression-level consumers of the checked raw-call action boundaries. *)
Theory rawCallExpressionPtr
Ancestors
  rawCallActionBindPtr exprPtrUnwrap exprSimHash wordArgsPtr

Theorem raw_call_action_frames:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ghost_kept cenv es sa G0 tn0 s0 J jn /\ wb_frame cenv es em sa s0 tm /\
  ghost_kept cenv em sm J jn tm Gmid kn /\ wb_frame cenv em em sm tm u /\
  ghost_kept cenv em sm Gmid kn u H un /\ wb_frame cenv em ee sm u t ==>
  ghost_kept cenv es sa G0 tn0 s0 H un /\ wb_frame cenv es ee sa s0 t
Proof
  strip_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 Gmid kn` by
    (irule ghost_kept_wb_trans >> metis_tac[]) >>
  `wb_frame cenv es em sa s0 u` by
    (mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s0`, `sa`, `em`, `em`, `sm`, `tm`, `u`, `ctx`]
       exprSimWordArgsTheory.wb_frame_trans) >> impl_tac >> simp[]) >>
  conj_tac
  >- (irule ghost_kept_wb_trans >> metis_tac[]) >>
  mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s0`, `sa`, `em`, `ee`, `sm`, `u`, `t`, `ctx`]
    exprSimWordArgsTheory.wb_frame_trans) >> impl_tac >> simp[]
QED

Theorem raw_call_stack_value_view_post:
  post_value_type cenv e = expr_type e /\
  stmt_state_rel ctx func cenv cx ee t /\
  expr_val_rel cx (expr_type e) v op t /\
  expr_val_at cenv cx (expr_type e) sa sb ee v op t /\
  wb_frame cenv es ee sa s0 t ==>
  vv_post ctx func cenv cx e es sa sb s0 ee (Value v) (StackValue ty op) t
Proof
  strip_tac >> irule vv_post_frame_intro >> asm_rewrite_tac[] >> simp[] >>
  simp[loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED

Theorem raw_call_memory_value_view_post:
  post_value_type cenv e = expr_type e /\ expr_type e = lowty /\ ~is_word_type (expr_type e) /\
  stmt_state_rel ctx func cenv cx ee t /\
  expr_val_rel cx (expr_type e) v op t /\
  expr_val_at cenv cx (expr_type e) sa sb ee v op t /\
  wb_frame cenv es ee sa s0 t ==>
  vv_post ctx func cenv cx e es sa sb s0 ee (Value v)
    (LocatedValue lowty (mk_ptr op LocMemory)) t
Proof
  strip_tac >> qpat_x_assum `expr_type e = lowty` (SUBST_ALL_TAC o SYM) >>
  irule vv_post_frame_intro >> asm_rewrite_tac[] >>
  qpat_x_assum `post_value_type _ _ = _` kall_tac >> simp[] >>
  rpt conj_tac >>
  fs[loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
    loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
    contextTheory.mk_ptr_def, vyperStateTheory.read_result_def,
    vyperStateTheory.return_def] >>
  rpt strip_tac >>
  qpat_x_assum `!tv. evaluate_type _ _ = SOME tv ==> _` (drule_then mp_tac) >>
  qpat_x_assum `!tv. evaluate_type _ _ = SOME tv /\ _ ==> _` (drule_then mp_tac) >>
  fs[]
QED

Theorem raw_call_vv_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx args /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  expr_vv_sim_ptr dep ctx PG func cenv cx ty
    (Call ann (RawCallTarget flags) args dflt) es
Proof
  strip_tac >> drule rawCallShapePtrTheory.raw_call_pre_operands >> strip_tac >>
  drule rawCallShapePtrTheory.raw_call_pre_flags >> strip_tac >> gvs[] >>
  simp[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >> rpt strip_tac >>
  drule rawCallShapePtrTheory.compile_expr_raw_call_steps >> strip_tac >> gvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4` by
    metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND,
      exprLoweringPropsTheory.ci_mono_emit_op] >>
  drule rawCallShapePtrTheory.raw_call_kwargs_types >> strip_tac >>
  drule_all rawCallShapePtrTheory.raw_call_kwargs_word_args >> strip_tac >>
  `!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[listTheory.EVERY_MEM, compileEnvTheory.is_word_type_def]) >>
  `expr_sim_inv cenv cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule exprSimPrecompilesTheory.typed_stack_args_shape >> metis_tac[]) >>
  drule_all exprSimWordArgsTheory.lower_word_args_shape_ready >> strip_tac >>
  suspend "compiler_chain"
QED

Resume raw_call_vv_sim_ptr[compiler_chain]:
  `ci_mono s4 s5` by simp[exprLoweringPropsTheory.ci_mono_def] >>
  `ci_mono s5 s6` by
    (Cases_on `go` >> gvs[] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND,
       exprLoweringPropsTheory.ci_mono_refl]) >>
  `ci_mono s6 s7 /\ ci_mono s7 sb` by
    (qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
     qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_raw_call_outbuf,
       exprLoweringPropsTheory.ci_mono_compile_raw_call_finish, pairTheory.SND]) >>
  `ci_mono sa s6` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\ fn_has_code s7 sb func` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  Cases_on `flags.rcf_max_outsize = 0`
  >- (Cases_on `flags.rcf_revert_on_failure`
      >- suspend "zero_reverting" >> suspend "scalar") >>
  Cases_on `flags.rcf_revert_on_failure`
  >- suspend "bytes" >> suspend "tuple"
QED

Resume raw_call_vv_sim_ptr[scalar]:
  gvs[] >> drule raw_call_scalar_action_outcome >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[] >>
  disch_then drule_all >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_id <= s6.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  drule_all raw_call_action_frames >> strip_tac >>
  qexists_tac `Value v` >>
  simp[vyperASTTheory.expr_type_def, vyperTypeSystemTheory.raw_call_return_type_def,
    compileEnvTheory.is_word_type_def, bodyPtrDefsTheory.ptr_vv_ok_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  irule raw_call_stack_value_view_post >>
  simp[vyperASTTheory.expr_type_def, vyperTypeSystemTheory.raw_call_return_type_def]
QED

Resume raw_call_vv_sim_ptr[zero_reverting]:
  gvs[] >> drule raw_call_zero_reverting_action_outcome >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[] >>
  disch_then drule_all >> disch_then (qspec_then `PG` assume_tac) >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_id <= s6.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  drule_all raw_call_action_frames >> strip_tac >>
  qexists_tac `Value v` >>
  simp[vyperASTTheory.expr_type_def, vyperTypeSystemTheory.raw_call_return_type_def,
    bodyPtrDefsTheory.ptr_vv_ok_def, vyperStateTheory.read_result_def,
    vyperStateTheory.return_def] >>
  irule raw_call_stack_value_view_post >>
  simp[vyperASTTheory.expr_type_def, vyperTypeSystemTheory.raw_call_return_type_def]
QED

Resume raw_call_vv_sim_ptr[bytes]:
  `0 < flags.rcf_max_outsize` by decide_tac >>
  gvs[] >> drule raw_call_bytes_action_outcome >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[] >>
  disch_then drule_all >> disch_then (qspec_then `PG` assume_tac) >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_id <= s6.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  drule_all raw_call_action_frames >> strip_tac >>
  qexists_tac `Value v` >>
  simp[vyperASTTheory.expr_type_def, vyperTypeSystemTheory.raw_call_return_type_def,
    bodyPtrDefsTheory.ptr_vv_ok_def, contextTheory.mk_ptr_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  reverse conj_tac
  >- gvs[bodyPtrDefsTheory.ptr_val_ok_def, compileEnvTheory.is_word_type_def,
         vyperTypeSystemTheory.raw_call_return_type_def] >>
  rewrite_tac[GSYM contextTheory.mk_ptr_def] >>
  irule raw_call_memory_value_view_post >> simp[vyperASTTheory.expr_type_def,
    compileEnvTheory.is_word_type_def]
QED

Resume raw_call_vv_sim_ptr[tuple]:
  `0 < flags.rcf_max_outsize` by decide_tac >>
  gvs[] >> drule raw_call_tuple_action_outcome >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[] >>
  disch_then drule_all >> disch_then (qspec_then `PG` assume_tac) >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_id <= s6.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  drule_all raw_call_action_frames >> strip_tac >>
  qexists_tac `Value v` >>
  simp[vyperASTTheory.expr_type_def, vyperTypeSystemTheory.raw_call_return_type_def,
    bodyPtrDefsTheory.ptr_vv_ok_def, contextTheory.mk_ptr_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  reverse conj_tac
  >- gvs[bodyPtrDefsTheory.ptr_val_ok_def, compileEnvTheory.is_word_type_def,
         vyperTypeSystemTheory.raw_call_return_type_def] >>
  rewrite_tac[GSYM contextTheory.mk_ptr_def] >>
  irule raw_call_memory_value_view_post >> simp[vyperASTTheory.expr_type_def,
    compileEnvTheory.is_word_type_def]
QED

Finalise raw_call_vv_sim_ptr

Theorem raw_call_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx args /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  expr_sim_ptr dep ctx PG func cenv cx ty
    (Call ann (RawCallTarget flags) args dflt) es
Proof
  strip_tac >> irule expr_sim_ptr_of_vv >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  irule raw_call_vv_sim_ptr >> metis_tac[]
QED
