(* Runtime entry specialization of the source evaluation exclusion.
   The conditional premise is discharged by the separate evaluate_ind join. *)
Theory loweringBudgetSourceEntryExclusion
Ancestors
  sourceCallCount e2eDefs supportedGetterProps bodyStorageCases
  supportedExprTraverse supportedStmtTraverse supportedProgram
  vyperInterpreter vyperState vyperContext compileVyper list pair

val _ = Parse.hide "body";

Theorem runtime_entry_no_create_outcome_error_from_eval:
  ((!cx s. ~supported_stmt_expr_exists expr_evm_run_root s /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt s) ==>
     !st st'. eval_stmt cx s st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx ss. ~supported_stmts_expr_exists expr_evm_run_root ss /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts ss) ==>
     !st st'. eval_stmts cx ss st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx it. ~supported_iterator_exists expr_evm_run_root it /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_iterator it) ==>
     !st st'. eval_iterator cx it st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx tyv nm ss vs. ~supported_stmts_expr_exists expr_evm_run_root ss /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts ss) ==>
     !st st'. eval_for cx tyv nm ss vs st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx e. ~supported_expr_exists expr_evm_run_root e /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) ==>
     !st st'. eval_expr cx e st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx es. EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)) es ==>
     !st st'. eval_exprs cx es st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx t. ~supported_target_exists expr_evm_run_root t /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_target t) ==>
     !st st'. eval_base_place cx t st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx t. ~supported_target_exists expr_evm_run_root t /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_target t) ==>
     !st st'. eval_target_place cx t st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx g v. ~supported_assignment_exists expr_evm_run_root g /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_atarget g) ==>
     !st st'. assign_tuple_targets cx g v st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx gs vs. ~supported_assignments_exists expr_evm_run_root gs /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_atargets gs) ==>
     !st st'. assign_tuple_target_list cx gs vs st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F) /\
  (!cx es. EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops /\
                IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)) es ==>
     !st st'. eval_expr_results cx es st = (INR (Error (RuntimeError "create outcome accounts")), st') ==> F)) ==>
  (!tops rpolicy unit am tx cd ret os obs res st.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\ valid_vyper_call tops tx cd ret /\
    call_entry_run os obs am tx = SOME (res,st) ==>
    res <> INR (Error (RuntimeError "create outcome accounts")))
Proof
  strip_tac >> rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `!cx ss. _ ==> !s t. eval_stmts cx ss s <> _` mp_tac >>
  rpt (pop_assum kall_tac) >> disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[valid_vyper_call_def] >>
  drule_all (cj 1 supported_selected_external_body) >>
  simp[supported_function_body_def] >> strip_tac >>
  drule (cj 2 supported_stmts_storage_syntax) >> strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `get_module_code cx NONE = SOME tops` by
    (simp[Abbr `cx`] >> metis_tac[source_deployment_context]) >>
  `!s t. eval_stmts cx body s <>
     (INR (Error (RuntimeError "create outcome accounts")),t)` by
    (qpat_x_assum `!cx ss. _ ==> !s t. eval_stmts cx ss s <> _` irule >> simp[] >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  `~cx.in_deploy /\ cx.txn = tx /\ cx.sources = am.sources` by
    simp[Abbr `cx`, initial_evaluation_context_def] >>
  gvs[source_deployment_rel_def] >>
  qpat_x_assum `call_entry_run _ _ _ _ = _` mp_tac >>
  simp[call_entry_run_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def, fn_entry_run_def, eval_external_defaults_def,
       Once evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
       vyperStateTheory.set_scopes_def, vyperStateTheory.finally_def,
       vyperStateTheory.return_def, lock_if_nr_def] >>
  gvs[type_env_all_modules_def, type_env_def, optionTheory.IS_SOME_EXISTS,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule vyperTypeContractSoundnessTheory.send_call_value_error >> simp[]
QED
