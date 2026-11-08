(* Successful argument casts establish the type of the original input.
   The identity interface is already exported by loweringHalt. *)
Theory entryReachBodyCastInputs
Ancestors
  loweringHalt vyperTyping

Theorem entry_safe_cast_input_typed:
  !tv v out.
    safe_cast tv v = SOME out ==> value_has_type tv v
Proof
  rpt strip_tac >>
  `out = v` by metis_tac[ safe_cast_some_eq ] >>
  metis_tac[ safe_cast_result_well_typed ]
QED
