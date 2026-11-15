Theory vyperPlaceInvariants
Ancestors
  list finite_map vyperState vyperTyping vyperTypeInvariants

(* Historical values are typed at their resolved, root-first paths, not at
   the current dynamic lengths. *)
Definition popped_history_typed_def:
  popped_history_typed tv history <=>
    !path v. MEM (path,v) history ==>
      ?ptv. subscripts_type tv path = SOME ptv /\
            well_formed_type_value ptv /\ value_has_type ptv v
End

Theorem popped_history_typed_nil[simp]:
  popped_history_typed tv []
Proof
  simp[popped_history_typed_def]
QED

Theorem popped_history_typed_cons:
  popped_history_typed tv ((path,v)::history) <=>
    (?ptv. subscripts_type tv path = SOME ptv /\
           well_formed_type_value ptv /\ value_has_type ptv v) /\
    popped_history_typed tv history
Proof
  simp[popped_history_typed_def] >> metis_tac[]
QED
