(* Keep the normal endpoint's running flag when a value outcome is bound. *)
Theory gasOutcomeFullRunning
Ancestors
  gasOutcomeFullCompose gasOutcomeFull venomState

Theorem gas_outcome_full_value_running:
  gas_outcome_full cfg tops cx st0 source start
    (\H res ee G tn t. ?v. res = INL v /\ Q H v ee G tn t) R ==>
  gas_outcome_full cfg tops cx st0 source start
    (\H res ee G tn t. ?v. res = INL v /\ ~t.vs_halted /\ Q H v ee G tn t) R
Proof
  PairCases_on `cfg` >> PairCases_on `start` >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
