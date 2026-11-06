Theory makeSsaCurrentForwardRuntime
Ancestors
  makeSsaCurrentRuntime makeSsaCurrentExecRuntime o1FrameLockstep venomExecSemantics

Theorem current_runtime_bind_last_slots_forward:
  state_rel sg st st' /\ current_last_output_slots sg outs outs' sg1 /\
  bind_outputs outs vals st = SOME t ==>
  ?t'. bind_outputs outs' vals st' = SOME t' /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `LENGTH outs = LENGTH outs'` by fs[current_last_output_slots_def] >>
  `LENGTH outs = LENGTH vals` by fs[bind_outputs_def] >>
  `?t'. bind_outputs outs' vals st' = SOME t'` by simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem current_exec_pure1_pair_forward:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure1 f inst st = OK t ==>
  ?t'. exec_pure1 f inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure1_def, AllCaseEqs()] >>
  Cases_on `inst'.inst_operands` >> gvs[] >>
  `LENGTH inst'.inst_outputs = 1` by
    fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_pure1_undefined_forward:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  exec_pure1 f inst st = Error "undefined operand" ==>
  exec_pure1 f inst' st' = Error "undefined operand"
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure1_def, AllCaseEqs()] >>
  Cases_on `inst'.inst_operands` >> gvs[]
QED
