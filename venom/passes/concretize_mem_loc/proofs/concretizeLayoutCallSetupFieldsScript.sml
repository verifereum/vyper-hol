Theory concretizeLayoutCallSetupFields
Ancestors concretizeLayoutSupplement calleeTransport venomExecSemantics
  venomState ptrDiscipline finite_map list pred_set

(* Paired setup resets halted on both sides; it need not preserve the
   caller's halted bit, nor require equal argument lists. *)
Theorem layout_setup_local_obs:
  concretize_local_obs s t /\
  setup_callee fn args s = SOME cs /\ setup_callee gn args' t = SOME ct ==>
  concretize_local_obs cs ct
Proof
  simp[setup_callee_def] >> rpt strip_tac >>
  gvs[concretize_local_obs_def, dead_result_rel_def]
QED

Theorem layout_setup_supplement:
  concretize_supplement D tn s t /\
  setup_callee fn args s = SOME cs /\ setup_callee gn args' t = SOME ct ==>
  concretize_supplement D (tn with t_var := FEMPTY) cs ct
Proof
  simp[setup_callee_def] >> rpt strip_tac >>
  gvs[concretize_supplement_def]
QED

Theorem layout_setup_static_fields:
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
  s.vs_initial_fmp = t.vs_initial_fmp /\
  setup_callee fn args s = SOME cs /\ setup_callee gn args' t = SOME ct ==>
  cs.vs_code = ct.vs_code /\ cs.vs_data_section = ct.vs_data_section /\
  cs.vs_initial_fmp = ct.vs_initial_fmp
Proof
  strip_tac >> dxrule setup_callee_shared_fields >> strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >> gvs[]
QED

val _ = export_theory();
