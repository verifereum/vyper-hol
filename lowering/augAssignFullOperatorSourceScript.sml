Theory augAssignFullOperatorSource
Ancestors
  stmtSimAugAssign bodyPtrBopSource
  vyperTypeSystem vyperTyping vyperValue vyperTypeBuiltins
  exprSimDefs vyperValueOperation

(* With the left type also the result type, equality can only compare bools.
   Other operators use the type-independent source boundary. *)
Theorem augassign_operator_source_representation:
  well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv cur /\
  evaluate_type (get_tenv cx) t2 = SOME tvR /\
  value_has_type tvR rhs ==>
  bop_result cx ty bop [ty;t2] cur rhs ee =
  case evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur rhs of
    INL v => INL v | INR err => INR (Error err)
Proof
  strip_tac >> irule bop_result_augassign >> simp[] >>
  strip_tac >> gvs[well_typed_binop_def, evaluate_type_def] >>
  Cases_on `cur` >> gvs[value_has_type_def]
QED

Theorem augassign_operator_source_value_type:
  well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv cur /\
  evaluate_type (get_tenv cx) t2 = SOME tvR /\
  value_has_type tvR rhs /\
  evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur rhs = INL v ==>
  value_has_type ptv v
Proof
  strip_tac >>
  metis_tac[well_typed_binop_success_type]
QED

Theorem augassign_operator_source_runtime_error:
  well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv cur /\
  evaluate_type (get_tenv cx) t2 = SOME tvR /\
  value_has_type tvR rhs /\
  evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur rhs = INR err ==>
  ?msg. err = RuntimeError msg /\
    bop_result cx ty bop [ty;t2] cur rhs ee =
      INR (Error (RuntimeError msg))
Proof
  strip_tac >>
  drule_all augassign_operator_source_representation >> simp[] >> strip_tac >>
  drule_all bop_typed_source_result_ok >>
  simp[expr_res_ok_def] >>
  strip_tac >- metis_tac[] >>
  qpat_x_assum `evaluate_binop _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `err = RevertData _` (SUBST_ALL_TAC) >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `bop` >> simp[evaluate_binop_def] >>
  simp[bounded_int_op_def, bounded_decimal_op_def, wrapped_int_op_def,
       oneline binop_negate_def, AllCaseEqs()]
QED
