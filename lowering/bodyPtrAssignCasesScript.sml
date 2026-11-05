(*
 * The pointer twin of bodySimMain's induction: the cases for declarations and assignments.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_annassign_case_ptr
 *   body_assign_case_ptr
 *   body_assign_tuple_case_ptr
 *   body_augassign_case_ptr
 *)
Theory bodyPtrAssignCases
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* ADMITTED: a piece of the body induction. *)
Theorem body_annassign_case_ptr:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ptr_ok cx e) ==>
    body_stmt_ptr_ok cx (AnnAssign id typ e)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_assign_case_ptr:
  !cx t e.
    (!s'' pv t'.
       eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ptr_ok cx t) /\
    body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (Assign (BaseTarget t) e)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_assign_tuple_case_ptr:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ptr_ok cx (TupleTarget gs) v) /\ body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (Assign (TupleTarget gs) e)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_augassign_case_ptr:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ptr_ok cx e) /\ body_base_target_ptr_ok cx t ==>
    body_stmt_ptr_ok cx (AugAssign ty t bop e)
Proof
  cheat
QED
