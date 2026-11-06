Theory lowerDloadReturnRestore
Ancestors
  lowerDloadSharedState o1LowerDloadJointRestore venomExecSemantics
  venomState ptrDiscipline finite_map pred_set

(* Retained environment comes from the caller; global observations and masks
   come from the current callee, never from the saved memory snapshot. *)
Theorem ld_shared_state_return_restore:
  ld_shared_state savedS savedT callerS callerT /\
  ld_shared_state tn un endS endT /\
  bind_outputs os xs (merge_callee_state callerS endS) = SOME s' /\
  bind_outputs ot xt (merge_callee_state callerT endT) = SOME t' ==>
  ld_shared_state (tn with t_var := ms) (un with t_var := mt) s' t'
Proof
  strip_tac >>
  dxrule ld_bind_outputs_vars_only >> disch_then SUBST1_TAC >>
  dxrule ld_bind_outputs_vars_only >> disch_then SUBST1_TAC >>
  fs[ld_shared_state_def, merge_callee_state_def]
QED
