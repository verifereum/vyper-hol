(* Active-module preconditions for the expressions of a linked Log. *)
Theory bodyLogArgPreMods
Ancestors
  bodyActiveStmtCallsMods bodyFullPredsMods bodyExprPreFacts
  bodyInvCodeProps bodyInvMetadataProps bodyInvModuleProps
  supportedStmts supportedExprs supportedStmtTraverse supportedExprTraverse
  allocLimits allocLimitsProps vyperTypeSystem vyperTypeCallGraph
  list pair

Theorem log_arg_pre_mods:
  !mods exps ctx cenv cx src tops bindings env env' id args ret_ty es.
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    supported_stmt tops bindings (Log id args) /\
    expr_sim_inv_mods mods cenv cx env es /\
    body_const_cells_agree_mods mods cx env es /\
    type_stmt env ret_ty (Log id args) = SOME env' /\
    stmt_exprs_ok cenv (Log id args) /\
    ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
      (Log id args) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Log id args) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
    call_evaluation_safe cx (int_calls_stmt (Log id args)) ==>
    !e st. MEM e args /\ expr_sim_inv_mods mods cenv cx env st ==>
      expr_body_pre_mods mods cenv cx env e st
Proof
  rpt gen_tac >> strip_tac >>
  `supported_log tops id args` by
    (qpat_assum `supported_stmt tops bindings (Log id args)` mp_tac >>
     simp_tac bool_ss [supported_stmt_def]) >>
  `supported_pure_exprs tops args` by
    (fs[supported_log_def] >> metis_tac[]) >>
  `well_typed_exprs env args` by
    fs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv args /\
   ~supported_exprs_exists
      (unallocated_bare_global_root cenv env) args /\
   ~supported_exprs_exists (const_name_root_mods mods) args /\
   ~supported_exprs_exists
      (\e. ~is_extcode e /\
        ~(byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e))) args /\
   (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
      EXISTS (occurs_abi_decode_target target o SND) mods) /\
   call_evaluation_safe cx (int_calls_exprs args)` by
    (drule_then assume_tac contract_inv_cenv_modules >>
     fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        int_calls_stmt_def, alloc_limits_stmt_def] >> metis_tac[]) >>
  `EVERY (\e. ~is_extcode e) args` by
    (rw[EVERY_MEM] >> rpt strip_tac >>
     metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode,
               exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  `EVERY (source_body_call_supported cx)
      (int_calls_stmt (Log id args))` by
    (drule_all_then assume_tac active_stmt_calls_resolve_mods >>
     pop_assum (fn th => assume_tac (CONJUNCT1 th)) >>
     first_x_assum (qspecl_then
       [`bindings`, `Log id args`, `ret_ty`, `env'`] mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `supported_pure_expr tops e` by
    (fs[supported_pure_exprs_every, EVERY_MEM] >> metis_tac[]) >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  `EVERY (source_body_call_supported cx) (int_calls_exprs args)` by
    (qpat_assum `EVERY (source_body_call_supported cx)
       (int_calls_stmt (Log id args))`
       (mp_tac o SIMP_RULE (srw_ss()) [int_calls_stmt_def]) >> simp[]) >>
  `supported_pure_expr tops e /\ ~is_extcode e /\
   well_typed_expr env e /\ alloc_limits_expr cenv e /\
   ~supported_expr_exists (const_name_root_mods mods) e /\
   ~supported_expr_exists
      (\x. ~is_extcode x /\
        ~(byte_widths_expr x /\ (array_slot_base cenv x \/ alloc_limits_expr cenv x))) e /\
   call_evaluation_safe cx (int_calls_expr e) /\
   ~expr_has_evm_run e /\
   EVERY (source_body_call_supported cx) (int_calls_expr e) /\
   (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
      EXISTS (occurs_abi_decode_target target o SND) mods)` by
    (conj_tac >- (fs[supported_pure_exprs_every, EVERY_MEM] >> metis_tac[]) >>
     conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
     conj_tac >- (drule_all_then ACCEPT_TAC exprSimSourceTheory.well_typed_exprs_member) >>
     conj_tac >- (drule_all_then ACCEPT_TAC exprSimSourceTheory.alloc_limits_exprs_mem) >>
     conj_tac >- (fs[supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
     conj_tac >- (fs[supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
     conj_tac >- (drule_all_then ACCEPT_TAC exprSimSourceTheory.call_evaluation_safe_exprs_mem) >>
     conj_tac >- (drule_then ACCEPT_TAC supportedExprTraverseTheory.supported_expr_no_evm_run) >>
     conj_tac >- (drule_all_then ACCEPT_TAC exprSimSourceTheory.int_calls_exprs_every_mem) >>
     rpt gen_tac >> disch_tac >>
     `supported_exprs_exists (expr_abi_decode_target_root target) args` by
       (rw[supportedExprTraverseTheory.supported_exprs_exists_every] >>
        simp[EXISTS_MEM] >> qexists_tac `e` >> simp[] >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!target. supported_exprs_exists
         (expr_abi_decode_target_root target) args ==> _`
       (qspecl_then [`target`] mp_tac) >> simp[] >> metis_tac[]) >>
  `~supported_expr_exists (unallocated_bare_global_root cenv env) e` by
    (fs[supported_stmt_expr_exists_def, supported_exprs_exists_every,
        EXISTS_MEM] >> metis_tac[]) >>
  `get_tenv cx = type_env_all_modules mods` by
    (drule_then ACCEPT_TAC contract_inv_type_env) >>
  irule stmt_expr_body_pre_mods >>
  rpt conj_tac >> simp[] >>
  qexists_tac `[]` >> simp[]

QED
