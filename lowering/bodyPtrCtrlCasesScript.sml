(*
 * The pointer twin of bodySimMain's induction: the cases for the control statements and statement lists.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_pass_case_ptr
 *   body_continue_case_ptr
 *   body_break_case_ptr
 *   body_if_case_ptr
 *   body_for_case_ptr
 *   body_expr_stmt_case_ptr
 *   body_stmts_nil_case_ptr
 *   body_stmts_cons_case_ptr
 *)
Theory bodyPtrCtrlCases
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* ADMITTED: a piece of the body induction. *)
Theorem body_pass_case_ptr:
  !cx. body_stmt_ptr_ok cx Pass
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_continue_case_ptr:
  !cx. body_stmt_ptr_ok cx Continue
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_break_case_ptr:
  !cx. body_stmt_ptr_ok cx Break
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_if_case_ptr:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ptr_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ptr_ok cx ss2) /\ body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (If e ss1 ss2)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_for_case_ptr:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ptr_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ptr_ok cx it) ==>
    body_stmt_ptr_ok cx (For id typ it n body)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_expr_stmt_case_ptr:
  !cx e. body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Expr e)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_stmts_nil_case_ptr:
  !cx. body_stmts_ptr_ok cx []
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_stmts_cons_case_ptr:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_ptr_ok cx ss) /\
    body_stmt_ptr_ok cx s ==>
    body_stmts_ptr_ok cx (s::ss)
Proof
  cheat
QED
