(*
 * The full body induction: bodySimPtrMainAt's body_sim_ptr_mutual_at over
 * bodyFullPreds's predicates, from bodyFullCases's cases, so a frame's
 * statements, statement lists and expressions simulate with source GAS
 * origins, memory bounds and pointer ghosts at one witness, for runtime
 * and constructor frames alike.
 *
 * TOP-LEVEL:
 *   body_sim_full_mutual -- the ten predicates, by evaluate_ind
 *   body_stmts_sim_full -- the statement-list judgment it gives
 *)
Theory bodySimFullMain
Ancestors bodyFullShadowBodyInv
  bodyFullCases bodyFullCreateHeld bodyFullIf bodyFullExprStmt bodyFullExits bodyFullPreds bodySimFull gasShadow bodySim supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph typedCopyMetadata alist list

val _ = Parse.hide "body";

val body_ind = evaluate_ind
  |> Q.SPECL [
       `\cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_stmt_full_ok cx s`,
       `\cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_stmts_full_ok cx ss`,
       `\cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_iterator_full_ok cx it`,
       `\cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_for_full_ok cx tyv nm body vs`,
       `\cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_expr_full_ok cx e`,
       `\cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_exprs_full_ok cx es`,
       `\cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_base_target_full_ok cx t`,
       `\cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_base_target_full_ok cx t`,
       `\cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_tuple_target_full_ok cx g v`,
       `\cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
          body_tuple_targets_full_ok cx gs vs`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV);

val full_case_simps =
  [push_function_def, return_def, vyperContextTheory.evaluation_context_accfupds,
   pairTheory.PAIR_EQ, sumTheory.INL_11];

fun full_case th =
  rpt strip_tac >> full_simp_tac bool_ss full_case_simps >>
  irule (SIMP_RULE bool_ss full_case_simps th) >>
  asm_rewrite_tac[] >> metis_tac[];

(* GATE_ADMISSION: missing case, RaiseCustomError body case; owner: gas-shadow/symbolic lane *)
Theorem body_raise_custom_case_full:
  !cx err.
    (!id positional kwargs tops params es.
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) ==>
    body_stmt_full_ok cx (Raise (RaiseCustomError err))
Proof
  cheat
QED

(* GATE_ADMISSION: missing case, AssertCustomError body case; owner: gas-shadow/symbolic lane *)
Theorem body_assert_custom_case_full:
  !cx e err.
    (!s tv t id positional kwargs tops params es.
       eval_expr cx e s = (INL tv,t) /\
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) /\
    body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assert e (AssertCustomError err))
Proof
  cheat
QED

Theorem body_sim_full_mutual:
  (!cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_stmt_full_ok cx s) /\
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_stmts_full_ok cx ss) /\
  (!cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_iterator_full_ok cx it) /\
  (!cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_for_full_ok cx tyv nm body vs) /\
  (!cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_expr_full_ok cx e) /\
  (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_exprs_full_ok cx es) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_base_target_full_ok cx t) /\
  (!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_tuple_target_full_ok cx g v) /\
  (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 ~internal_defaults_const_names tops /\
                 ~supportedProgram$internal_defaults_msg_gas tops) ==>
    body_tuple_targets_full_ok cx gs vs)
Proof
  mp_tac body_ind >> impl_tac
  >- (rpt conj_tac >| [
    (* 0 *) full_case body_pass_case_full,
    (* 1 *) full_case body_continue_case_full,
    (* 2 *) full_case body_break_case_full,
    (* 3 *) full_case body_return_none_case_full,
    (* 4 *) full_case body_return_case_full,
    (* 5 *) full_case body_raise_bare_case_full,
    (* 6 *) full_case body_raise_unreachable_case_full,
    (* 7 *) full_case body_raise_reason_case_full,
    (* 8 *) full_case body_raise_custom_case_full,
    (* 9 *) full_case body_assert_case_full,
    (* 10 *) full_case body_assert_unreachable_case_full,
    (* 11 *) full_case body_assert_reason_case_full,
    (* 12 *) full_case body_assert_custom_case_full,
    (* 13 *) full_case body_log_case_full,
    (* 14 *) full_case body_annassign_case_full,
    (* 15 *) full_case body_append_case_full,
    (* 16 *) full_case body_assign_case_full,
    (* 17 *) full_case body_assign_tuple_case_full,
    (* 18 *) full_case body_augassign_case_full,
    (* 19 *) full_case body_if_case_full,
    (* 20 *) full_case body_for_case_full,
    (* 21 *) full_case body_expr_stmt_case_full,
    (* 22 *) full_case body_stmts_nil_case_full,
    (* 23 *) full_case body_stmts_cons_case_full,
    (* 24 *) simp[body_iterator_full_ok_def],
    (* 25 *) rpt strip_tac >> fs[] >> rw[body_iterator_full_ok_def] >> metis_tac[],
    (* 26 *) simp[body_for_full_ok_def],
    (* 27 *) rpt strip_tac >> fs[] >> rw[body_for_full_ok_def] >> first_x_assum irule >> simp[push_scope_with_var_def, return_def] >> metis_tac[],
    (* 28 *) rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[],
    (* 29 *) rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[],
    (* 30 *) rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[],
    (* 31 *) full_case body_ifexp_case_full,
    (* 32 *) rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[],
    (* 33 *) full_case body_structlit_case_full,
    (* 34 *) full_case body_subscript_case_full,
    (* 35 *) full_case body_attribute_case_full,
    (* 36 *) full_case body_builtin_case_full,
    (* 37 *) full_case body_pop_case_full,
    (* 38 *) full_case body_type_builtin_case_full,
    (* 39 *) full_case body_send_case_full,
    (* 40 *) full_case body_extcall_case_full,
    (* 41 *) full_case body_intcall_case_full,
    (* 42 *) full_case body_raw_call_case_full,
    (* 43 *) full_case body_raw_call_calldata_case_full,
    (* 44 *) full_case body_raw_log_case_full,
    (* 45 *) full_case body_raw_revert_case_full,
    (* 46 *) full_case body_selfdestruct_case_full,
    (* CREATE *) rpt gen_tac >> Cases_on `kind` >>
          rpt strip_tac >> full_simp_tac bool_ss full_case_simps >>
          metis_tac[create_minimal_proxy_expr_full_ok, create_copy_expr_full_ok,
            create_blueprint_expr_full_ok, raw_create_expr_full_ok],
    (* 48 *) simp[body_exprs_full_ok_def],
    (* 49 *) rpt strip_tac >> fs[] >> rw[body_exprs_full_ok_def] >> metis_tac[],
    (* 50 *) simp[body_base_target_full_ok_def],
    (* 51 *) simp[body_base_target_full_ok_def],
    (* 52 *) simp[body_base_target_full_ok_def],
    (* 53 *) rpt strip_tac >> fs[] >> rw[body_base_target_full_ok_def] >> metis_tac[],
    (* 54 *) simp[],
    (* 55 *) simp[body_tuple_target_full_ok_def],
    (* 56 *) simp[body_tuple_target_full_ok_def],
    (* 57 *) simp[body_tuple_target_full_ok_def],
    (* 58 *) rpt strip_tac >> fs[] >> rw[body_tuple_target_full_ok_def] >> metis_tac[],
    (* 59 *) simp[body_tuple_target_full_ok_def],
    (* 60 *) simp[body_tuple_target_full_ok_def]
  ]) >>
  simp[]
QED

Theorem body_stmts_sim_full:
  !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv cx env env'
   ret_ty lctx RetQ ss es.
    ~internal_defaults_const_names tops /\
    ~supportedProgram$internal_defaults_msg_gas tops /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ struct_args_unique tops /\
    supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (stmts_env cenv lctx ret_ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  rpt strip_tac >>
  `!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
        struct_args_unique ts /\
        ~internal_defaults_const_names ts /\
        ~supportedProgram$internal_defaults_msg_gas ts` by (fs[body_inv_def] >> metis_tac[]) >>
  metis_tac[body_sim_full_mutual, body_stmts_full_ok_def]
QED
