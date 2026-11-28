(* Request-prefix companion to bodySimFullMain. *)
Theory s1PrefixBodySimFullMain
Ancestors
  s1PrefixPreds bodySimFullMain s1PrefixDefs s1PrefixCases
  s1PrefixBoolChainSelectedStmtCasePorts
  s1PrefixBodyMutualInduction s1PrefixBodyStmtsSpecialize

val _ = Parse.hide "body";

Theorem body_sim_prefix_mutual:
  (!cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_stmt s) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmt_loop_calls_ok [(NONE,tops)] s) ==>
    body_stmt_prefix_ok cx s) /\
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_stmts ss) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
    body_stmts_prefix_ok cx ss) /\
  (!cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_iterator it) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_iterator_prefix_ok cx it) /\
  (!cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_stmts body) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] body) ==>
    body_for_prefix_ok cx tyv nm body vs) /\
  (!cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_expr e) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_expr_prefix_ok cx e) /\
  (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_exprs es) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_exprs_prefix_ok cx es) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_target t) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_base_target_prefix_ok cx t) /\
  (!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_atarget g) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_target_prefix_ok cx g v) /\
  (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_atargets gs) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_targets_prefix_ok cx gs vs)
Proof
  MATCH_MP_TAC body_sim_prefix_mutual_from_cases >> rpt conj_tac
  >- ACCEPT_TAC body_assign_case_prefix
  >- ACCEPT_TAC body_assign_tuple_case_prefix
  >- ACCEPT_TAC body_for_case_prefix
  >- ACCEPT_TAC body_builtin_case_prefix
  >- ACCEPT_TAC body_intcall_case_prefix
  >- ACCEPT_TAC body_raw_call_calldata_case_prefix
QED

Theorem body_stmts_sim_prefix:
  !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv cx env env'
   ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (vyperTypeCallGraph$int_calls_stmts ss) /\
    shadow_body_inv tops ctx shadow_ctx /\ struct_args_unique tops /\
    supported_stmts tops bindings ss /\
    (!vis mut nr raw fn args dflts ret body.
       MEM (FunctionDecl vis mut nr raw fn args dflts ret body) tops ==>
       stmts_loop_calls_ok [(NONE,tops)] body) /\
    stmts_loop_calls_ok [(NONE,tops)] ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  ACCEPT_TAC (MP body_stmts_sim_prefix_from_list_clause
    (CONJUNCT1 (CONJUNCT2 body_sim_prefix_mutual)))
QED
