(*
 * The pointer twin of bodySimMain's induction: the cases for return, raise and assert.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_return_none_case_ptr
 *   body_return_case_ptr
 *   body_raise_bare_case_ptr
 *   body_raise_unreachable_case_ptr
 *   body_raise_reason_case_ptr
 *   body_assert_case_ptr
 *   body_assert_unreachable_case_ptr
 *   body_assert_reason_case_ptr
 *)
Theory bodyPtrExitCases
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* ADMITTED: a piece of the body induction. *)
Theorem body_return_none_case_ptr:
  !cx. body_stmt_ptr_ok cx (Return NONE)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_return_case_ptr:
  !cx e. body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Return (SOME e))
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_raise_bare_case_ptr:
  !cx. body_stmt_ptr_ok cx (Raise RaiseBare)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_raise_unreachable_case_ptr:
  !cx. body_stmt_ptr_ok cx (Raise RaiseUnreachable)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_raise_reason_case_ptr:
  !cx e. body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Raise (RaiseReason e))
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_assert_case_ptr:
  !cx e. body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Assert e AssertBare)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_assert_unreachable_case_ptr:
  !cx e.
    body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Assert e AssertUnreachable)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_assert_reason_case_ptr:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ptr_ok cx se) /\
    body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (Assert e (AssertReason se))
Proof
  cheat
QED
