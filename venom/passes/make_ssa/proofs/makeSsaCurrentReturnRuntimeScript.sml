Theory makeSsaCurrentReturnRuntime
Ancestors
  makeSsaCurrentRuntime o1FrameLockstep venomExecSemantics stateFrame
  venomState finite_map list tailMergeStep
Theorem current_return_merge_state_rel:
  state_rel sg st st' /\ execution_frame e' = execution_frame e ==>
  state_rel sg (adopt_return_fmp ret (merge_callee_state st e))
    (adopt_return_fmp ret (merge_callee_state st' e'))
Proof
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def, state_rel_def,
    vars_rel_def, lookup_var_def, execution_frame_def,
    venom_state_component_equality] >> metis_tac[]
QED

Theorem current_return_merge_lookup:
  lookup_var v (adopt_return_fmp ret (merge_callee_state st e)) = lookup_var v st
Proof
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def, lookup_var_def]
QED

Theorem current_return_bind_last_slots:
  state_rel sg st st' /\ execution_frame e' = execution_frame e /\
  current_last_output_slots sg outs outs' sg1 /\
  bind_outputs outs' ret.iret_values
    (adopt_return_fmp ret (merge_callee_state st' e')) = SOME t' ==>
  ?t. bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state st e)) = SOME t /\
    state_rel sg1 t t'
Proof
  strip_tac >> irule current_runtime_bind_last_slots >>
  goal_assum $ drule_at Any >> simp[] >>
  qexists_tac `sg` >> simp[] >>
  irule current_return_merge_state_rel >>
  gvs[execution_frame_def, venom_state_component_equality]
QED

Theorem current_return_bind_unwritten:
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state st e)) = SOME t /\
  ~MEM v outs ==> lookup_var v t = lookup_var v st
Proof
  strip_tac >> drule bind_outputs_lookup_outside >>
  simp[current_return_merge_lookup]
QED

Theorem current_return_bind_written:
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state st e)) = SOME t /\
  MEM v outs ==> IS_SOME (lookup_var v t)
Proof
  metis_tac[current_runtime_bind_lookup_written_general]
QED
