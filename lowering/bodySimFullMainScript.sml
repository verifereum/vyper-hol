(*
 * The full body induction: bodySimPtrMainAt's body_sim_ptr_mutual_at over
 * bodyFullPreds's predicates, from bodyFullCases's cases, so a frame's
 * statements, statement lists and expressions simulate with source GAS
 * origins, memory bounds and pointer ghosts at one witness, for runtime
 * and constructor frames alike.
 *
 * TOP-LEVEL:
 *   body_sim_full_mutual -- the eleven predicates, by evaluate_ind
 *   body_stmts_sim_full -- the statement-list judgment it gives
 *)
Theory bodySimFullMain
Ancestors
  bodyFullCases bodyFullPreds bodySimFull gasShadow bodySim supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph list

val _ = Parse.hide "body";

val body_ind = evaluate_ind
  |> Q.SPECL [`body_stmt_full_ok`, `body_stmts_full_ok`, `body_iterator_full_ok`,
              `body_for_full_ok`, `body_expr_full_ok`, `body_exprs_full_ok`,
              `body_base_target_full_ok`, `body_base_target_full_ok`,
              `body_tuple_target_full_ok`, `body_tuple_targets_full_ok`,
              `body_results_full_ok`];

Theorem body_sim_full_mutual:
  (!cx s. body_stmt_full_ok cx s) /\ (!cx ss. body_stmts_full_ok cx ss) /\
  (!cx it. body_iterator_full_ok cx it) /\
  (!cx tyv nm body vs. body_for_full_ok cx tyv nm body vs) /\
  (!cx e. body_expr_full_ok cx e) /\ (!cx es. body_exprs_full_ok cx es) /\
  (!cx t. body_base_target_full_ok cx t) /\
  (!cx g v. body_tuple_target_full_ok cx g v) /\
  (!cx gs vs. body_tuple_targets_full_ok cx gs vs) /\
  (!cx es. body_results_full_ok cx es)
Proof
  mp_tac body_ind >> impl_tac
  >- (rpt conj_tac >| [
    (* 0 *) MATCH_ACCEPT_TAC body_pass_case_full,
    (* 1 *) MATCH_ACCEPT_TAC body_continue_case_full,
    (* 2 *) MATCH_ACCEPT_TAC body_break_case_full,
    (* 3 *) MATCH_ACCEPT_TAC body_return_none_case_full,
    (* 4 *) MATCH_ACCEPT_TAC body_return_case_full,
    (* 5 *) MATCH_ACCEPT_TAC body_raise_bare_case_full,
    (* 6 *) MATCH_ACCEPT_TAC body_raise_unreachable_case_full,
    (* 7 *) MATCH_ACCEPT_TAC body_raise_reason_case_full,
    (* 8 *) rw[body_stmt_full_ok_def, supported_stmt_def, supported_raise_reason_def],
    (* 9 *) MATCH_ACCEPT_TAC body_assert_case_full,
    (* 10 *) MATCH_ACCEPT_TAC body_assert_unreachable_case_full,
    (* 11 *) MATCH_ACCEPT_TAC body_assert_reason_case_full,
    (* 12 *) rw[body_stmt_full_ok_def, supported_stmt_def, supported_assert_reason_def],
    (* 13 *) MATCH_ACCEPT_TAC body_log_case_full,
    (* 14 *) MATCH_ACCEPT_TAC body_annassign_case_full,
    (* 15 *) MATCH_ACCEPT_TAC body_append_case_full,
    (* 16 *) MATCH_ACCEPT_TAC body_assign_case_full,
    (* 17 *) MATCH_ACCEPT_TAC body_assign_tuple_case_full,
    (* 18 *) MATCH_ACCEPT_TAC body_augassign_case_full,
    (* 19 *) MATCH_ACCEPT_TAC body_if_case_full,
    (* 20 *) MATCH_ACCEPT_TAC body_for_case_full,
    (* 21 *) MATCH_ACCEPT_TAC body_expr_stmt_case_full,
    (* 22 *) MATCH_ACCEPT_TAC body_stmts_nil_case_full,
    (* 23 *) MATCH_ACCEPT_TAC body_stmts_cons_case_full,
    (* 24 *) simp[body_iterator_full_ok_def],
    (* 25 *) rw[body_iterator_full_ok_def] >> metis_tac[],
    (* 26 *) simp[body_for_full_ok_def],
    (* 27 *) rw[body_for_full_ok_def] >> first_x_assum irule >> simp[push_scope_with_var_def, return_def],
    (* 28 *) rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[],
    (* 29 *) rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[],
    (* 30 *) rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[],
    (* 31 *) MATCH_ACCEPT_TAC body_ifexp_case_full,
    (* 32 *) rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[],
    (* 33 *) MATCH_ACCEPT_TAC body_structlit_case_full,
    (* 34 *) MATCH_ACCEPT_TAC body_subscript_case_full,
    (* 35 *) MATCH_ACCEPT_TAC body_attribute_case_full,
    (* 36 *) MATCH_ACCEPT_TAC body_builtin_case_full,
    (* 37 *) MATCH_ACCEPT_TAC body_pop_case_full,
    (* 38 *) MATCH_ACCEPT_TAC body_type_builtin_case_full,
    (* 39 *) MATCH_ACCEPT_TAC body_send_case_full,
    (* 40 *) MATCH_ACCEPT_TAC body_extcall_case_full,
    (* 41 *) MATCH_ACCEPT_TAC body_intcall_case_full,
    (* 42 *) MATCH_ACCEPT_TAC body_raw_call_case_full,
    (* 43 *) MATCH_ACCEPT_TAC body_raw_call_calldata_case_full,
    (* 44 *) MATCH_ACCEPT_TAC body_raw_log_case_full,
    (* 45 *) MATCH_ACCEPT_TAC body_raw_revert_case_full,
    (* 46 *) MATCH_ACCEPT_TAC body_selfdestruct_case_full,
    (* 47 *) MATCH_ACCEPT_TAC body_create_case_full,
    (* 48 *) simp[body_exprs_full_ok_def],
    (* 49 *) rw[body_exprs_full_ok_def] >> metis_tac[],
    (* 50 *) simp[body_base_target_full_ok_def],
    (* 51 *) simp[body_base_target_full_ok_def],
    (* 52 *) simp[body_base_target_full_ok_def],
    (* 53 *) rw[body_base_target_full_ok_def] >> metis_tac[],
    (* 54 *) simp[],
    (* 55 *) simp[body_tuple_target_full_ok_def],
    (* 56 *) simp[body_tuple_target_full_ok_def],
    (* 57 *) simp[body_tuple_target_full_ok_def],
    (* 58 *) rw[body_tuple_target_full_ok_def] >> metis_tac[],
    (* 59 *) simp[body_tuple_target_full_ok_def],
    (* 60 *) simp[body_tuple_target_full_ok_def],
    (* 61 *) simp[body_results_full_ok_def],
    (* 62 *) rw[body_results_full_ok_def] >> metis_tac[]
  ]) >>
  simp[]
QED

Theorem body_stmts_sim_full:
  !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv cx env env'
   ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (stmts_env cenv lctx ret_ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  metis_tac[body_sim_full_mutual, body_stmts_full_ok_def]
QED
