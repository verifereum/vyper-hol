(* The existing O1 state contract applies to the non-static shadow. *)
Theory staticShadowO1State
Ancestors
  staticShadowDefs o1PassContract unitTransformDefs lowerDloadDefs venomState

Theorem static_shadow_o1_run_state_ok:
  o1_initial_state_ok s /\ s.vs_fmp = s.vs_initial_fmp /\
  code_layout_valid s ==> o1_run_state_ok (static_shadow s)
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def, code_layout_valid_def,
       static_shadow_def]
QED
