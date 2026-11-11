(*
 * The pointer twin of bodySimMain's induction: the cases for log and append.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_log_case_ptr
 *   body_append_case_ptr
 *)
Theory bodyPtrLogCases
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list bodyAppendStoragePtr
  supportedStmts

val _ = Parse.hide "body";

(* ADMITTED: a piece of the body induction. *)
Theorem body_log_case_ptr:
  !cx id es. body_exprs_ptr_ok cx es ==> body_stmt_ptr_ok cx (Log id es)
Proof
  cheat
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_append_case_ptr:
  !cx t e.
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_ptr_ok cx e) /\
    body_base_target_ptr_ok cx t ==>
    body_stmt_ptr_ok cx (Append t e)
Proof
  rpt strip_tac >> Cases_on `?nid. t = TopLevelNameTarget nid`
  >- (gvs[] >> irule body_append_storage_other_ptr >> first_assum ACCEPT_TAC) >>
  Cases_on `t` >> gvs[] >>
  rw[body_stmt_ptr_ok_def, supported_stmt_def, supported_append_target_def]
QED
