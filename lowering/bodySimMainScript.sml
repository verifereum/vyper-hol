(*
 * The body simulation of S1 (#636, #637, #638)
 *
 * body_sim_mutual: by evaluate_ind, every statement, statement list and
 * expression of a frame of the lowered program simulates (bodySim's
 * predicates), internal calls included.  Each case of the induction is a
 * case lemma of bodySimStmtCases, bodySimLog, bodySimDeclCases or
 * bodySimExprCases, or a short tactic below.  bodySimEntry gives
 * ce_locals_declared at a body's entry.
 *
 * TOP-LEVEL:
 *   body_sim_mutual  — the eleven predicates, by evaluate_ind
 *   body_stmts_sim, body_stmt_sim, body_expr_sim — the judgments it gives
 *)

Theory bodySimMain
Ancestors
  list bodySim bodySimStmtCases bodySimDeclCases bodySimExprCases
  bodySimCallCases
  bodySimEntry bodySimLog stmtSimIf
  supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph

val body_ind = evaluate_ind
  |> Q.SPECL [`body_stmt_ok`, `body_stmts_ok`, `body_iterator_ok`,
              `body_for_ok`, `body_expr_ok`, `body_exprs_ok`,
              `body_base_target_ok`, `body_base_target_ok`,
              `body_tuple_target_ok`, `body_tuple_targets_ok`,
              `body_results_ok`];

(* ===== The induction ===== *)

Theorem body_sim_mutual:
  (!cx s. body_stmt_ok cx s) /\ (!cx ss. body_stmts_ok cx ss) /\
  (!cx it. body_iterator_ok cx it) /\
  (!cx tyv nm body vs. body_for_ok cx tyv nm body vs) /\
  (!cx e. body_expr_ok cx e) /\ (!cx es. body_exprs_ok cx es) /\
  (!cx t. body_base_target_ok cx t) /\
  (!cx g v. body_tuple_target_ok cx g v) /\
  (!cx gs vs. body_tuple_targets_ok cx gs vs) /\
  (!cx es. body_results_ok cx es)
Proof
  cheat
QED

(* ===== The judgments it gives ===== *)

Theorem body_stmts_sim:
  !tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es res es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ret_ty ss)
      (eval_stmts cx ss) es
Proof
  cheat
QED

Theorem body_stmt_sim:
  !tops bindings ctx func cenv cx env env' ret_ty lctx RetQ s es res es'.
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings s /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) s ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ret_ty s)
      (eval_stmt cx s) es
Proof
  cheat
QED

(* compile_expr_sim without its int_calls_expr e = [], in a frame of the
   lowered program. *)
Theorem body_expr_sim:
  !tops ctx func cenv cx env ty e es.
    body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
    expr_sim ctx func cenv cx ty e es /\ expr_vv_sim ctx func cenv cx ty e es
Proof
  cheat
QED
