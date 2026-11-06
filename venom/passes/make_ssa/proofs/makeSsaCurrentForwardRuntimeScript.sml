Theory makeSsaCurrentForwardRuntime
Ancestors
  makeSsaCurrentRuntime venomExecSemantics

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
