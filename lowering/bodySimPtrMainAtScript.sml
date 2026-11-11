(*
 * The (D, lo) body induction: bodySimPtrMain's body_sim_ptr_mutual over
 * bodyPtrPredsAt's predicates, from bodyPtrCasesAt's cases (admitted
 * until ported), for runtime and constructor frames alike.
 *
 * TOP-LEVEL:
 *   body_sim_ptr_mutual_at -- the eleven predicates, by evaluate_ind
 *   body_stmts_sim_ptr_at -- the statement-list judgment it gives, the
 *     (D, lo) twin of bodyStmtsSimPtr's body_stmts_sim_ptr
 *)
Theory bodySimPtrMainAt
Ancestors
  bodyPtrCasesAt bodyPtrPredsAt bodyPtrDefs bodySim supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph list

val _ = Parse.hide "body";

val body_ind = evaluate_ind
  |> Q.SPECL [`body_stmt_ptr_ok_at`, `body_stmts_ptr_ok_at`, `body_iterator_ptr_ok_at`,
              `body_for_ptr_ok_at`, `body_expr_ptr_ok_at`, `body_exprs_ptr_ok_at`,
              `body_base_target_ptr_ok_at`, `body_base_target_ptr_ok_at`,
              `body_tuple_target_ptr_ok_at`, `body_tuple_targets_ptr_ok_at`,
              `body_results_ptr_ok_at`];

Theorem body_sim_ptr_mutual_at:
  (!cx s. body_stmt_ptr_ok_at cx s) /\ (!cx ss. body_stmts_ptr_ok_at cx ss) /\
  (!cx it. body_iterator_ptr_ok_at cx it) /\
  (!cx tyv nm body vs. body_for_ptr_ok_at cx tyv nm body vs) /\
  (!cx e. body_expr_ptr_ok_at cx e) /\ (!cx es. body_exprs_ptr_ok_at cx es) /\
  (!cx t. body_base_target_ptr_ok_at cx t) /\
  (!cx g v. body_tuple_target_ptr_ok_at cx g v) /\
  (!cx gs vs. body_tuple_targets_ptr_ok_at cx gs vs) /\
  (!cx es. body_results_ptr_ok_at cx es)
Proof
  mp_tac body_ind >> impl_tac
  >- (rpt conj_tac >| [
    (* 0 *) MATCH_ACCEPT_TAC body_pass_case_ptr_at,
    (* 1 *) MATCH_ACCEPT_TAC body_continue_case_ptr_at,
    (* 2 *) MATCH_ACCEPT_TAC body_break_case_ptr_at,
    (* 3 *) MATCH_ACCEPT_TAC body_return_none_case_ptr_at,
    (* 4 *) MATCH_ACCEPT_TAC body_return_case_ptr_at,
    (* 5 *) MATCH_ACCEPT_TAC body_raise_bare_case_ptr_at,
    (* 6 *) MATCH_ACCEPT_TAC body_raise_unreachable_case_ptr_at,
    (* 7 *) MATCH_ACCEPT_TAC body_raise_reason_case_ptr_at,
    (* 8 *) rw[body_stmt_ptr_ok_def, supported_stmt_def, supported_raise_reason_def],
    (* 9 *) MATCH_ACCEPT_TAC body_assert_case_ptr_at,
    (* 10 *) MATCH_ACCEPT_TAC body_assert_unreachable_case_ptr_at,
    (* 11 *) MATCH_ACCEPT_TAC body_assert_reason_case_ptr_at,
    (* 12 *) rw[body_stmt_ptr_ok_def, supported_stmt_def, supported_assert_reason_def],
    (* 13 *) MATCH_ACCEPT_TAC body_log_case_ptr_at,
    (* 14 *) MATCH_ACCEPT_TAC body_annassign_case_ptr_at,
    (* 15 *) MATCH_ACCEPT_TAC body_append_case_ptr_at,
    (* 16 *) MATCH_ACCEPT_TAC body_assign_case_ptr_at,
    (* 17 *) MATCH_ACCEPT_TAC body_assign_tuple_case_ptr_at,
    (* 18 *) MATCH_ACCEPT_TAC body_augassign_case_ptr_at,
    (* 19 *) MATCH_ACCEPT_TAC body_if_case_ptr_at,
    (* 20 *) MATCH_ACCEPT_TAC body_for_case_ptr_at,
    (* 21 *) MATCH_ACCEPT_TAC body_expr_stmt_case_ptr_at,
    (* 22 *) MATCH_ACCEPT_TAC body_stmts_nil_case_ptr_at,
    (* 23 *) MATCH_ACCEPT_TAC body_stmts_cons_case_ptr_at,
    (* 24 *) simp[body_iterator_ptr_ok_def],
    (* 25 *) rw[body_iterator_ptr_ok_def] >> metis_tac[],
    (* 26 *) simp[body_for_ptr_ok_def],
    (* 27 *) rw[body_for_ptr_ok_def] >> first_x_assum irule >> simp[push_scope_with_var_def, return_def],
    (* 28 *) rpt strip_tac >> irule body_expr_ptr_ok_at_leaf >> simp[],
    (* 29 *) rpt strip_tac >> irule body_expr_ptr_ok_at_leaf >> simp[],
    (* 30 *) rpt strip_tac >> irule body_expr_ptr_ok_at_leaf >> simp[],
    (* 31 *) MATCH_ACCEPT_TAC body_ifexp_case_ptr_at,
    (* 32 *) rpt strip_tac >> irule body_expr_ptr_ok_at_leaf >> simp[],
    (* 33 *) MATCH_ACCEPT_TAC body_structlit_case_ptr_at,
    (* 34 *) MATCH_ACCEPT_TAC body_subscript_case_ptr_at,
    (* 35 *) MATCH_ACCEPT_TAC body_attribute_case_ptr_at,
    (* 36 *) rpt strip_tac >> irule body_builtin_case_ptr_at >> conj_tac
               >- (rpt strip_tac >> Cases_on `bt = Bop In \/ bt = Bop NotIn` >>
                   metis_tac[]) >> metis_tac[],
    (* 37 *) MATCH_ACCEPT_TAC body_pop_case_ptr_at,
    (* 38 *) MATCH_ACCEPT_TAC body_type_builtin_case_ptr_at,
    (* 39 *) MATCH_ACCEPT_TAC body_send_case_ptr_at,
    (* 40 *) MATCH_ACCEPT_TAC body_extcall_case_ptr_at,
    (* 41 *) MATCH_ACCEPT_TAC body_intcall_case_ptr_at,
    (* 42 *) MATCH_ACCEPT_TAC body_raw_call_case_ptr_at,
    (* 43 *) MATCH_ACCEPT_TAC body_raw_call_calldata_case_ptr_at,
    (* 44 *) MATCH_ACCEPT_TAC body_raw_log_case_ptr_at,
    (* 45 *) MATCH_ACCEPT_TAC body_raw_revert_case_ptr_at,
    (* 46 *) MATCH_ACCEPT_TAC body_selfdestruct_case_ptr_at,
    (* 47 *) MATCH_ACCEPT_TAC body_create_case_ptr_at,
    (* 48 *) simp[body_exprs_ptr_ok_def],
    (* 49 *) rw[body_exprs_ptr_ok_def] >> metis_tac[],
    (* 50 *) simp[body_base_target_ptr_ok_def],
    (* 51 *) simp[body_base_target_ptr_ok_def],
    (* 52 *) simp[body_base_target_ptr_ok_def],
    (* 53 *) rw[body_base_target_ptr_ok_def] >> metis_tac[],
    (* 54 *) simp[],
    (* 55 *) simp[body_tuple_target_ptr_ok_def],
    (* 56 *) simp[body_tuple_target_ptr_ok_def],
    (* 57 *) simp[body_tuple_target_ptr_ok_def],
    (* 58 *) rw[body_tuple_target_ptr_ok_def] >> metis_tac[],
    (* 59 *) simp[body_tuple_target_ptr_ok_def],
    (* 60 *) simp[body_tuple_target_ptr_ok_def],
    (* 61 *) simp[body_results_ptr_ok_def],
    (* 62 *) rw[body_results_ptr_ok_def] >> metis_tac[]
  ]) >>
  simp[]
QED

Theorem body_stmts_sim_ptr_at:
  !D lo d PG tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_ptr_at D lo d ctx PG func cx RetQ cenv ret_ty ==>
    stmt_frag_ptr_at D lo d ctx PG func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) (eval_stmts cx ss) es
Proof
  metis_tac[body_sim_ptr_mutual_at, body_stmts_ptr_ok_def]
QED
