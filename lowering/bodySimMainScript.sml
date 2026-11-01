(*
 * The body simulation of S1 (#636, #637, #638)
 *
 * body_sim_mutual: by evaluate_ind, every statement, statement list and
 * expression of a frame of the lowered program simulates (bodySim's
 * predicates), internal calls included.  Each case of the induction is a
 * case lemma of bodySimStmtCases, bodySimDeclCases or bodySimExprCases, or
 * a short tactic below.  bodySimEntry gives ce_locals_declared at a body's
 * entry.
 *
 * TOP-LEVEL:
 *   body_sim_mutual  — the eleven predicates, by evaluate_ind
 *   body_stmts_sim, body_stmt_sim, body_expr_sim — the judgments it gives
 *)

Theory bodySimMain
Ancestors
  list bodySim bodySimStmtCases bodySimDeclCases bodySimExprCases
  bodySimEntry stmtSimIf
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
  mp_tac body_ind >> impl_tac
  >- (rpt conj_tac >| [
    (* 0 *) MATCH_ACCEPT_TAC body_pass_case,
    (* 1 *) MATCH_ACCEPT_TAC body_continue_case,
    (* 2 *) MATCH_ACCEPT_TAC body_break_case,
    (* 3 *) MATCH_ACCEPT_TAC body_return_none_case,
    (* 4 *) MATCH_ACCEPT_TAC body_return_case,
    (* 5 *) rw[body_stmt_ok_def] >> irule compile_raise_frag >> simp[],
    (* 6 *) rw[body_stmt_ok_def] >> irule compile_raise_frag >> simp[],
    (* 7 *) MATCH_ACCEPT_TAC body_raise_reason_case,
    (* 8 *) rw[body_stmt_ok_def, supported_stmt_def, supported_raise_reason_def],
    (* 9 *) rpt strip_tac >> irule body_assert_case >> simp[],
    (* 10 *) rpt strip_tac >> irule body_assert_case >> simp[],
    (* 11 *) MATCH_ACCEPT_TAC body_assert_reason_case,
    (* 12 *) rw[body_stmt_ok_def, supported_stmt_def, supported_assert_reason_def],
    (* 13 *) MATCH_ACCEPT_TAC body_log_case,
    (* 14 *) MATCH_ACCEPT_TAC body_annassign_case,
    (* 15 *) MATCH_ACCEPT_TAC body_append_case,
    (* 16 *) MATCH_ACCEPT_TAC body_assign_case,
    (* 17 *) MATCH_ACCEPT_TAC body_assign_tuple_case,
    (* 18 *) MATCH_ACCEPT_TAC body_augassign_case,
    (* 19 *) MATCH_ACCEPT_TAC body_if_case,
    (* 20 *) MATCH_ACCEPT_TAC body_for_case,
    (* 21 *) MATCH_ACCEPT_TAC body_expr_stmt_case,
    (* 22 *) MATCH_ACCEPT_TAC body_stmts_nil_case,
    (* 23 *) MATCH_ACCEPT_TAC body_stmts_cons_case,
    (* 24 *) simp[body_iterator_ok_def],
    (* 25 *) rw[body_iterator_ok_def] >> metis_tac[],
    (* 26 *) simp[body_for_ok_def],
    (* 27 *) rw[body_for_ok_def] >> first_x_assum irule >> simp[push_scope_with_var_def, return_def],
    (* 28 *) rpt strip_tac >> irule body_expr_ok_intro >> simp[int_calls_expr_def],
    (* 29 *) rpt strip_tac >> irule body_expr_ok_intro >> simp[int_calls_expr_def],
    (* 30 *) rpt strip_tac >> irule body_expr_ok_intro >> simp[int_calls_expr_def],
    (* 31 *) MATCH_ACCEPT_TAC body_ifexp_case,
    (* 32 *) rpt strip_tac >> irule body_expr_ok_intro >> simp[int_calls_expr_def],
    (* 33 *) MATCH_ACCEPT_TAC body_structlit_case,
    (* 34 *) MATCH_ACCEPT_TAC body_subscript_case,
    (* 35 *) MATCH_ACCEPT_TAC body_attribute_case,
    (* 36 *) MATCH_ACCEPT_TAC body_builtin_case,
    (* 37 *) MATCH_ACCEPT_TAC body_pop_case,
    (* 38 *) MATCH_ACCEPT_TAC body_type_builtin_case,
    (* 39 *) MATCH_ACCEPT_TAC body_send_case,
    (* 40 *) MATCH_ACCEPT_TAC body_extcall_case,
    (* 41 *) MATCH_ACCEPT_TAC body_intcall_case,
    (* 42 *) MATCH_ACCEPT_TAC body_raw_call_case,
    (* 43 *) MATCH_ACCEPT_TAC body_raw_call_calldata_case,
    (* 44 *) MATCH_ACCEPT_TAC body_raw_log_case,
    (* 45 *) MATCH_ACCEPT_TAC body_raw_revert_case,
    (* 46 *) MATCH_ACCEPT_TAC body_selfdestruct_case,
    (* 47 *) MATCH_ACCEPT_TAC body_create_case,
    (* 48 *) simp[body_exprs_ok_def],
    (* 49 *) rw[body_exprs_ok_def] >> metis_tac[],
    (* 50 *) simp[body_base_target_ok_def],
    (* 51 *) simp[body_base_target_ok_def],
    (* 52 *) simp[body_base_target_ok_def],
    (* 53 *) rw[body_base_target_ok_def] >> metis_tac[],
    (* 54 *) simp[],
    (* 55 *) simp[body_tuple_target_ok_def],
    (* 56 *) simp[body_tuple_target_ok_def],
    (* 57 *) simp[body_tuple_target_ok_def],
    (* 58 *) rw[body_tuple_target_ok_def] >> metis_tac[],
    (* 59 *) simp[body_tuple_target_ok_def],
    (* 60 *) simp[body_tuple_target_ok_def],
    (* 61 *) simp[body_results_ok_def],
    (* 62 *) rw[body_results_ok_def] >> metis_tac[]
  ]) >>
  simp[]
QED

(* ===== The judgments it gives ===== *)

Theorem body_stmts_sim:
  !tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es res es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
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
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
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
