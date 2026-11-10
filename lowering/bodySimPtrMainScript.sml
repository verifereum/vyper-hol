(*
 * The pointer twin of bodySimMain's body induction (S3)
 *
 * body_sim_ptr_mutual: by evaluate_ind, every statement, statement list
 * and expression of a frame of the lowered program simulates with the
 * ghost (bodyPtrPreds's predicates), internal calls included.  Each case
 * is a case lemma of the bodyPtr*Cases theories, or a short tactic below,
 * as in bodySimMain.  The leaf expressions come from exprSimPtr's
 * leaf_expr_sim_ptr, through body_expr_ptr_ok_leaf.
 *
 * TOP-LEVEL:
 *   body_sim_ptr_mutual -- the eleven predicates, by evaluate_ind
 *   body_expr_ptr_ok_leaf -- the leaf expressions are body_expr_ptr_ok
 *   body_stmts_ptr_ok_sim -- the statement-list judgment it gives
 *)
Theory bodySimPtrMain
Ancestors
  bodyPtrCtrlCases bodyPtrExitCases bodyPtrAssignCases bodyPtrLogCases bodyPtrExprCases bodyPtrIntCallCase bodyPtrCallCases exprSimPtr
  bodyPtrPreds bodyPtrDefs bodySim exprSimSource supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem body_expr_ptr_ok_leaf:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_ptr_ok cx e
Proof
  rpt gen_tac >> disch_tac >> simp[body_expr_ptr_ok_def] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >> rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env e es` by
    (simp[expr_sim_pre_body] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[int_calls_expr_def]) >>
  metis_tac[leaf_expr_sim_ptr]
QED

val body_ind = evaluate_ind
  |> Q.SPECL [`body_stmt_ptr_ok`, `body_stmts_ptr_ok`, `body_iterator_ptr_ok`,
              `body_for_ptr_ok`, `body_expr_ptr_ok`, `body_exprs_ptr_ok`,
              `body_base_target_ptr_ok`, `body_base_target_ptr_ok`,
              `body_tuple_target_ptr_ok`, `body_tuple_targets_ptr_ok`,
              `body_results_ptr_ok`];

Theorem body_sim_ptr_mutual:
  (!cx s. body_stmt_ptr_ok cx s) /\ (!cx ss. body_stmts_ptr_ok cx ss) /\
  (!cx it. body_iterator_ptr_ok cx it) /\
  (!cx tyv nm body vs. body_for_ptr_ok cx tyv nm body vs) /\
  (!cx e. body_expr_ptr_ok cx e) /\ (!cx es. body_exprs_ptr_ok cx es) /\
  (!cx t. body_base_target_ptr_ok cx t) /\
  (!cx g v. body_tuple_target_ptr_ok cx g v) /\
  (!cx gs vs. body_tuple_targets_ptr_ok cx gs vs) /\
  (!cx es. body_results_ptr_ok cx es)
Proof
  mp_tac body_ind >> impl_tac
  >- (rpt conj_tac >| [
    (* 0 *) MATCH_ACCEPT_TAC body_pass_case_ptr,
    (* 1 *) MATCH_ACCEPT_TAC body_continue_case_ptr,
    (* 2 *) MATCH_ACCEPT_TAC body_break_case_ptr,
    (* 3 *) MATCH_ACCEPT_TAC body_return_none_case_ptr,
    (* 4 *) MATCH_ACCEPT_TAC body_return_case_ptr,
    (* 5 *) MATCH_ACCEPT_TAC body_raise_bare_case_ptr,
    (* 6 *) MATCH_ACCEPT_TAC body_raise_unreachable_case_ptr,
    (* 7 *) MATCH_ACCEPT_TAC body_raise_reason_case_ptr,
    (* 8 *) rw[body_stmt_ptr_ok_def, supported_stmt_def, supported_raise_reason_def],
    (* 9 *) MATCH_ACCEPT_TAC body_assert_case_ptr,
    (* 10 *) MATCH_ACCEPT_TAC body_assert_unreachable_case_ptr,
    (* 11 *) MATCH_ACCEPT_TAC body_assert_reason_case_ptr,
    (* 12 *) rw[body_stmt_ptr_ok_def, supported_stmt_def, supported_assert_reason_def],
    (* 13 *) MATCH_ACCEPT_TAC body_log_case_ptr,
    (* 14 *) MATCH_ACCEPT_TAC body_annassign_case_ptr,
    (* 15 *) MATCH_ACCEPT_TAC body_append_case_ptr,
    (* 16 *) MATCH_ACCEPT_TAC body_assign_case_ptr,
    (* 17 *) MATCH_ACCEPT_TAC body_assign_tuple_case_ptr,
    (* 18 *) MATCH_ACCEPT_TAC body_augassign_case_ptr,
    (* 19 *) MATCH_ACCEPT_TAC body_if_case_ptr,
    (* 20 *) MATCH_ACCEPT_TAC body_for_case_ptr,
    (* 21 *) MATCH_ACCEPT_TAC body_expr_stmt_case_ptr,
    (* 22 *) MATCH_ACCEPT_TAC body_stmts_nil_case_ptr,
    (* 23 *) MATCH_ACCEPT_TAC body_stmts_cons_case_ptr,
    (* 24 *) simp[body_iterator_ptr_ok_def],
    (* 25 *) rw[body_iterator_ptr_ok_def] >> metis_tac[],
    (* 26 *) simp[body_for_ptr_ok_def],
    (* 27 *) rw[body_for_ptr_ok_def] >> first_x_assum irule >> simp[push_scope_with_var_def, return_def],
    (* 28 *) rpt strip_tac >> irule body_expr_ptr_ok_leaf >> simp[],
    (* 29 *) rpt strip_tac >> irule body_expr_ptr_ok_leaf >> simp[],
    (* 30 *) rpt strip_tac >> irule body_expr_ptr_ok_leaf >> simp[],
    (* 31 *) MATCH_ACCEPT_TAC body_ifexp_case_ptr,
    (* 32 *) rpt strip_tac >> irule body_expr_ptr_ok_leaf >> simp[],
    (* 33 *) MATCH_ACCEPT_TAC body_structlit_case_ptr,
    (* 34 *) MATCH_ACCEPT_TAC body_subscript_case_ptr,
    (* 35 *) MATCH_ACCEPT_TAC body_attribute_case_ptr,
    (* 36 *) rpt strip_tac >> irule body_builtin_case_ptr >> conj_tac
               >- (rpt strip_tac >> Cases_on `bt = Bop In \/ bt = Bop NotIn` >>
                   metis_tac[]) >> metis_tac[],
    (* 37 *) MATCH_ACCEPT_TAC body_pop_case_ptr,
    (* 38 *) MATCH_ACCEPT_TAC body_type_builtin_case_ptr,
    (* 39 *) MATCH_ACCEPT_TAC body_send_case_ptr,
    (* 40 *) MATCH_ACCEPT_TAC body_extcall_case_ptr,
    (* 41 *) MATCH_ACCEPT_TAC body_intcall_case_ptr,
    (* 42 *) MATCH_ACCEPT_TAC body_raw_call_case_ptr,
    (* 43 *) MATCH_ACCEPT_TAC body_raw_call_calldata_case_ptr,
    (* 44 *) MATCH_ACCEPT_TAC body_raw_log_case_ptr,
    (* 45 *) MATCH_ACCEPT_TAC body_raw_revert_case_ptr,
    (* 46 *) MATCH_ACCEPT_TAC body_selfdestruct_case_ptr,
    (* 47 *) MATCH_ACCEPT_TAC body_create_case_ptr,
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

Theorem body_stmts_ptr_ok_sim:
  !d PG tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) (eval_stmts cx ss) es
Proof
  metis_tac[body_sim_ptr_mutual, body_stmts_ptr_ok_def]
QED
