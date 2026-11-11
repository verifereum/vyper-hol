(* Source replay for replacing a subvalue of the current immutable root. *)
Theory immutableWriteReplay
Ancestors
  vyperState vyperContext finite_map alist

Theorem immutable_replace_write_replay:
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,a) /\
  assign_subscripts tv a path (Replace v) = INL updated ==>
  write_place cx (ImmutablePlace src id path) v es =
    (INL (), es with immutables :=
      (cx.txn.target, set_source_immutables src
        (get_source_immutables src imms |+ (id,(tv,updated))) imms) ::
      ADELKEY cx.txn.target es.immutables)
Proof
  strip_tac >>
  simp[write_place_def, get_immutables_def, get_address_immutables_def,
       set_immutable_def, set_address_immutables_def,
       bind_def, ignore_bind_def, return_def, lift_option_type_def, lift_sum_def] >>
  simp[evaluation_state_component_equality]
QED
