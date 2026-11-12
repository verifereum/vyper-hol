(* Shared caller restoration derived from successful source callee execution. *)
Theory functionInlinerLiveReturn
Ancestors
  functionInlinerSharedResume functionInlinerEvaluatorResidual functionInlinerFmp

Theorem inline_source_return_fmp_resume:
  inliner_input_ok C /\
  lookup_function nm C.ctx_functions = SOME callee /\
  setup_callee callee args saved = SOME cs /\
  run_blocks fuel C callee cs = IntRet ir u /\
  inline_shared_frame u = inline_shared_frame t ==>
  t.vs_fmp = (case ir.iret_adopt_fmp of NONE => saved.vs_fmp | SOME p => p)
Proof
  strip_tac >>
  `inline_fmp_ctx_ok C` by metis_tac[inline_input_fmp_ctx] >>
  drule_all inline_callee_fmp_result >>
  disch_then (qspec_then `fuel` mp_tac) >>
  simp[inline_fmp_result_def] >> strip_tac >>
  `t.vs_fmp = saved.vs_fmp` by
    gvs[functionInlinerFrameTheory.inline_shared_frame_def,
        stateFrameTheory.execution_frame_def,
        venomStateTheory.venom_state_component_equality] >>
  simp[]
QED

Theorem inline_source_return_shared_resume:
  inliner_input_ok C /\
  lookup_function nm C.ctx_functions = SOME callee /\
  setup_callee callee args saved = SOME cs /\
  run_blocks fuel C callee cs = IntRet ir u /\ ~cs.vs_halted /\
  inline_shared_frame u = inline_shared_frame t /\
  inline_caller_residual t = inline_caller_residual saved ==>
  inline_shared_frame (adopt_return_fmp ir (merge_callee_state saved u)) =
  inline_shared_frame t
Proof
  strip_tac >> irule inline_shared_resume >> simp[] >>
  drule_all inline_source_return_fmp_resume >> simp[]
QED

Theorem inline_source_return_shared_bind_jump:
  inliner_input_ok C /\
  lookup_function nm C.ctx_functions = SOME callee /\
  setup_callee callee args saved = SOME cs /\
  run_blocks fuel C callee cs = IntRet ir u /\ ~cs.vs_halted /\
  inline_shared_frame u = inline_shared_frame t /\
  inline_caller_residual t = inline_caller_residual saved /\
  bind_outputs outs ir.iret_values saved = SOME caller' /\
  bind_outputs dests ir.iret_values t = SOME t' ==>
  inline_shared_frame (adopt_return_fmp ir (merge_callee_state caller' u)) =
  inline_shared_frame (jump_to ret t')
Proof
  strip_tac >> irule inline_shared_resume_bind_jump >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  drule_all inline_source_return_fmp_resume >> simp[]
QED
