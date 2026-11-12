(* Shared-state companion of storage-only selected-return transport.
   Caller residual and optional FMP evidence are supplied by the consumer. *)
Theory functionInlinerSharedResume
Ancestors
  functionInlinerSimulation functionInlinerFrame stateFrame
  venomExecSemantics venomInstProofs1 venomState

Theorem inline_shared_resume:
  inline_caller_residual t = inline_caller_residual saved /\
  inline_shared_frame s = inline_shared_frame t /\
  t.vs_fmp = (case ir.iret_adopt_fmp of NONE => saved.vs_fmp | SOME p => p)
  ==>
  inline_shared_frame (adopt_return_fmp ir (merge_callee_state saved s)) =
  inline_shared_frame t
Proof
  Cases_on `ir.iret_adopt_fmp` >>
  simp[inline_caller_residual_def, inline_shared_frame_def,
       execution_frame_def, merge_callee_state_def, adopt_return_fmp_def,
       venom_state_component_equality]
QED

Theorem inline_shared_resume_bind_jump:
  bind_outputs outs vals saved = SOME caller' /\
  bind_outputs dests vals t = SOME t' /\
  inline_caller_residual t = inline_caller_residual saved /\
  inline_shared_frame s = inline_shared_frame t /\
  t.vs_fmp = (case ir.iret_adopt_fmp of NONE => saved.vs_fmp | SOME p => p)
  ==>
  inline_shared_frame (adopt_return_fmp ir (merge_callee_state caller' s)) =
  inline_shared_frame (jump_to ret t')
Proof
  strip_tac >>
  `inline_shared_frame caller' = inline_shared_frame saved` by
    (irule bind_outputs_preserves >> simp[] >> goal_assum (drule_at Any)) >>
  `inline_shared_frame t' = inline_shared_frame t` by
    (irule bind_outputs_preserves >> simp[] >> goal_assum (drule_at Any)) >>
  `caller'.vs_fmp = saved.vs_fmp` by
    (irule bind_outputs_preserves >> simp[update_var_def] >>
     goal_assum (drule_at Any)) >>
  `inline_caller_residual t = inline_caller_residual caller'` by
    metis_tac[inline_caller_residual_shared] >>
  `inline_shared_frame (jump_to ret t') = inline_shared_frame t` by
    gvs[inline_shared_frame_def, execution_frame_def, jump_to_def] >>
  simp[] >> irule inline_shared_resume >> simp[]
QED
