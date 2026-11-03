(* Source selection boundaries for array read simulation. *)
Theory exprSimArraySubscript
Ancestors
  exprSimNoPop exprSimArrayIndex vyperPlaceResultTyping vyperState

(* A current-value path takes priority over every historical snapshot. *)
Theorem read_memory_path_current_append:
  !entry path tv v suffix w.
    subscripts_type entry.type path = SOME tv /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    evaluate_subscripts tv v suffix = INL w ==>
    read_memory_path entry (path ++ suffix) = INL w
Proof
  rpt strip_tac >>
  drule_all evaluate_subscripts_append >>
  simp[read_memory_path_def]
QED

(* Evaluation alone does not imply that the declared subscript type exists. *)
Theorem evaluate_subscripts_untyped_success[local]:
  evaluate_subscripts NoneTV (ArrayV (TupleV [IntV 0]))
    [ValueSubscript (IntV 0)] = INL (IntV 0) /\
  subscript_type NoneTV (ValueSubscript (IntV 0)) = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem read_memory_path_current_append_typed:
  !entry path tv v suffix w.
    value_has_type entry.type entry.value /\
    well_formed_type_value entry.type /\
    subscripts_type entry.type path = SOME tv /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    evaluate_subscripts tv v suffix = INL w ==>
    ?wtv. subscripts_type entry.type (path ++ suffix) = SOME wtv /\
      well_formed_type_value wtv /\ value_has_type wtv w /\
      evaluate_subscripts entry.type entry.value (path ++ suffix) = INL w /\
      read_memory_path entry (path ++ suffix) = INL w
Proof
  rpt strip_tac >>
  `evaluate_subscripts entry.type entry.value (path ++ suffix) = INL w` by
    (drule_all evaluate_subscripts_append >> simp[]) >>
  `read_memory_path entry (path ++ suffix) = INL w` by
    simp[read_memory_path_def] >>
  simp[] >>
  irule vyperPlaceStatePreservationTheory.evaluate_subscripts_declared_type_exists >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED
