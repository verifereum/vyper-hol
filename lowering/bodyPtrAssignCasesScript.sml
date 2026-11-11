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
  annAssignPtrDispatch annAssignPtrWord annAssignPtrFacts supportedStmts compileEnv
  bodyPtrAssignResidual bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
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
  rw[body_stmt_ptr_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  Cases_on `is_word_type typ`
  >- (irule body_annassign_word_ptr >> metis_tac[]) >>
  `0 < type_memory_bytes cenv typ` by
    metis_tac[annassign_memory_bytes_pos_ptr] >>
  Cases_on `lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)`
  >- (Cases_on `lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
                 has_length_word typ /\ is_empty_value_expr e`
      >- (irule body_annassign_memory_ptr >> metis_tac[]) >>
      `type_widens_to env.type_defs (expr_type e) typ` by
        gvs[type_stmt_def, AllCaseEqs()] >>
      `lowered_value_type cenv e = expr_type e` by
        metis_tac[type_widens_to_def, arg_type_fits_bytestring_target] >>
      irule body_annassign_widened_aggregate_ptr >> gvs[] >> metis_tac[]) >>
  irule body_annassign_widened_aggregate_call_ptr >> metis_tac[]
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
