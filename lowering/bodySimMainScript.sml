(*
 * The body simulation of S1 (#636, #637, #638).
 *
 * body_sim_mutual: every statement, statement list and expression of a
 * frame of the lowered program simulates, internal calls included.
 * bodySimBound proves its cases by the interpreter's termination bounds,
 * supplying ordinary-expression IHs even when AbiEncode uses ABI traversal.
 *
 * TOP-LEVEL:
 *   body_sim_mutual — the unchanged public simulation predicates
 *   body_stmts_sim, body_stmt_sim, body_expr_sim — the judgments it gives
 *)

Theory bodySimMain
Ancestors
  list bodySim bodySimBound stmtSimIf supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph

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
  metis_tac[body_sim_bounded]
QED

(* ===== The judgments it gives ===== *)

Theorem body_stmts_sim:
  !tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es res es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    expr_sim_inv cenv cx env es /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmts cx ss es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ret_ty ss)
      es res es'
Proof
  metis_tac[body_sim_mutual, body_stmts_ok_def]
QED

Theorem body_stmt_sim:
  !tops bindings ctx func cenv cx env env' ret_ty lctx RetQ s es res es'.
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings s /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx s es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ret_ty s)
      es res es'
Proof
  metis_tac[body_sim_mutual, body_stmt_ok_def]
QED

(* compile_expr_sim without its int_calls_expr e = [], in a frame of the
   lowered program. *)
Theorem body_expr_sim:
  !tops ctx func cenv cx env ty e es.
    body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
    expr_sim ctx func cenv cx ty e es /\ expr_vv_sim ctx func cenv cx ty e es
Proof
  metis_tac[body_sim_mutual, body_expr_ok_def]
QED
