(* Restrict the linked induction's call guard to the actual operand list.
 * Only the static guard is transported; evaluation stays in interpreter order. *)
Theory bodyCustomErrorOperandsMods
Ancestors
  bodyStorageCases vyperAST vyperTypeCallGraph list sorting

Theorem custom_error_ordered_calls_every:
  order_custom_error_args params err = SOME es /\
  EVERY P (int_calls_exprs (custom_error_exprs err)) ==>
  EVERY P (int_calls_exprs es)
Proof
  simp[body_exprs_main_calls_every] >> strip_tac >>
  drule order_custom_error_args_perm >>
  disch_then (irule o iffLR o MATCH_MP PERM_EVERY) >>
  first_assum ACCEPT_TAC
QED

Theorem raise_custom_ordered_calls_every:
  order_custom_error_args params err = SOME es /\
  EVERY P (int_calls_stmt (Raise (RaiseCustomError err))) ==>
  EVERY P (int_calls_exprs es)
Proof
  simp[int_calls_stmt_def, int_calls_raise_reason_def] >>
  metis_tac[custom_error_ordered_calls_every]
QED

Theorem assert_custom_ordered_calls_every:
  order_custom_error_args params err = SOME es /\
  EVERY P (int_calls_stmt (Assert e (AssertCustomError err))) ==>
  EVERY P (int_calls_exprs es)
Proof
  simp[int_calls_stmt_def, int_calls_assert_reason_def, EVERY_APPEND] >>
  metis_tac[custom_error_ordered_calls_every]
QED
