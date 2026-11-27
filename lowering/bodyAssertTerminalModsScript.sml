(* The terminal assertion/raise fragments for a linked body.  The bare
   assertion fragment is supplied by bodyBareAssertMods; this theory selects
   the literal or nonliteral RaiseReason fragment at the actual source. *)
Theory bodyAssertTerminalMods
Ancestors
  bodyBareAssertMods bodyRaiseReasonLiteralMods bodyRaiseReasonNonliteralMods
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodySimFull
  bodyInvSplit bodySim supportedStmts supportedExprTraverse supportedStmtTraverse
  compileEnv vyperInterpreter vyperState vyperAST list

val _ = Parse.hide "body";

Theorem compile_raise_reason_frag_full_mods:
  !mods exps cx e DF lo d PG src tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_expr_full_ok_mods mods exps cx e /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    supported_stmt tops bindings (Raise (RaiseReason e)) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Raise (RaiseReason e)) ==>
       EXISTS (occurs_abi_decode_target target o SND) mods) /\
    body_const_cells_agree_mods mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseReason e)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
    ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
      (Raise (RaiseReason e)) /\
    (!key. MEM (vyperSubscriptOverlap$WriteAcc
                  (vyperSubscriptOverlap$StateRef key))
                (vyperSubscriptOverlap$accesses_stmt (Raise (RaiseReason e))) /\
             IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
             IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
    frame_ret_ok_full_mods mods
      (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full_mods
      (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Raise (RaiseReason e))))
      (eval_stmt cx (Raise (RaiseReason e))) es
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?ml str. e = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >>
      irule compile_raise_reason_literal_frag_full_mods >>
      conj_tac
      >- (qexistsl_tac [`env`,`env'`] >>
          qpat_assum `type_stmt _ _ _ = SOME _` ACCEPT_TAC)
      >- qpat_assum `stmt_exprs_ok _ _` ACCEPT_TAC) >>
  irule compile_raise_reason_nonliteral_frag_full_mods >>
  rpt conj_tac >> rpt (first_assum ACCEPT_TAC) >> metis_tac[]
QED
