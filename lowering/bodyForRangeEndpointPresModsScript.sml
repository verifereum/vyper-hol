(* Source preconditions for the checked Range operands in the outer environment. *)
Theory bodyForRangeEndpointPresMods
Ancestors
  bodyActiveStmtCallsMods bodyFullForFacts bodyInvCodeProps bodyInvMetadataProps
  bodyExprPreFacts bodySim supportedStmtTraverse supportedExprTraverse
  allocLimits allocLimitsProps vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness list

val _ = Parse.hide "body";

Theorem range_endpoint_pres_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  supported_stmt tops bindings (For id typ (Range e1 e2) bound body) /\
  type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
  expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
  stmt_exprs_ok cenv (For id typ (Range e1 e2) bound body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (For id typ (Range e1 e2) bound body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Range e1 e2) bound body) ==>
    EXISTS (occurs_abi_decode_target target o SND) mods) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Range e1 e2) bound body)) ==>
  expr_body_pre_mods mods cenv cx env e1 es /\
  (!ee. expr_sim_inv_mods mods cenv cx env ee ==> expr_body_pre_mods mods cenv cx env e2 ee)
Proof
  strip_tac >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (For id typ (Range e1 e2) bound body))` by
    (drule_all_then strip_assume_tac active_stmt_calls_resolve_mods >>
     first_x_assum irule >> conj_tac
     >- (qexistsl_tac [`env'`, `ret_ty`] >> simp[]) >>
     qexists_tac `bindings` >> simp[]) >>
  drule_then assume_tac supported_stmt_body_safe >>
  drule_then assume_tac type_stmt_for_projection >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  qpat_x_assum `stmt_exprs_ok _ _` (strip_assume_tac o SIMP_RULE std_ss
    [stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_iterator_def,
     supported_stmt_expr_exists_def, supported_iterator_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `body_stmt_safe _ _` (strip_assume_tac o SIMP_RULE std_ss
    [body_stmt_safe_def, supported_stmt_expr_exists_def,
     supported_iterator_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` (strip_assume_tac o SIMP_RULE std_ss
    [supported_stmt_expr_exists_def, supported_iterator_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `!target. supported_stmt_expr_exists _ _ ==> _`
    (strip_assume_tac o SIMP_RULE std_ss
      [supported_stmt_expr_exists_def, supported_iterator_exists_def,
       DISJ_IMP_THM, FORALL_AND_THM]) >>
  qpat_x_assum `EVERY (source_body_call_supported _) _`
    (strip_assume_tac o REWRITE_RULE [int_calls_stmt_def, int_calls_iterator_def, EVERY_APPEND]) >>
  `call_evaluation_safe cx (int_calls_expr e1) /\ call_evaluation_safe cx (int_calls_expr e2)` by
    (qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
     simp[int_calls_stmt_def, int_calls_iterator_def] >>
     metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]) >>
  fs[well_typed_iterator_def] >>
  conj_tac >> rpt strip_tac >>
  irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre_mods)) >>
  simp[expr_has_evm_run_def, DE_MORGAN_THM, LEFT_AND_OVER_OR, supported_expr_exists_disj] >>
  (conj_tac >- (irule alloc_limits_expr_not_extcode >> goal_assum (drule_at Any)) >>
   conj_tac >-
     (qpat_assum `cenv.ce_modules = mods` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
   irule (cj 1 alloc_limits_expr_exists) >> simp[])
QED
