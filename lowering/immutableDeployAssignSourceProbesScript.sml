(* Interface probe: a root immutable write preserves its stored type. *)
Theory immutableDeployAssignSourceProbes
Ancestors
  vyperState

Theorem immutable_root_write_set:
  get_immutables cx src es = (INL imms,es) /\
  FLOOKUP imms id = SOME (tv,old) ==>
  write_place cx (ImmutablePlace src id []) v es =
    set_immutable cx src id tv v es
Proof
  strip_tac >>
  simp[write_place_def, bind_def, lift_option_type_def, lift_sum_def,
       assign_subscripts_def, return_def]
QED
