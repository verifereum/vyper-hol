(*
 * Storage well-formedness across an expression of a function body
 *
 * exprStoragePreservation keeps contract_storage_well_formed across an
 * expression with no internal calls.  A body's expression may make
 * internal calls, and the callee's statements then run too.  In a
 * supported program no function body has raw_call or create
 * (supported_expr_no_evm_run) and every internal call is to the main
 * module, whose code is the program, so in oracle mode (IS_SOME
 * st.outcomes) nothing the callee runs needs a postulate about EVM code
 * either: external calls and send take the oracle's outcomes, which keep
 * storage well formed by oracle_storage_ok, and storage writes keep it by
 * the source semantics.
 *
 * TOP-LEVEL:
 *   eval_expr_body_oracle_storage — across an expression
 *   eval_stmts_body_oracle_storage — across a supported statement, or a
 *     list of them (supported_stmt gives the same syntactic facts)
 *)

Theory bodyStoragePreservation
Ancestors
  list pair vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeExprSoundness vyperTypeCallStackSoundness vyperTypeInvariants
  vyperStorageLayoutSafety vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperCallOutcomeStorage
  vyperEvalOutcomeSuffix supportedExprTraverse supportedProgram
  exprOracleStoragePreservation exprOracleStorageInterfaces
  stmtOracleStoragePreservation bodyOracleCallStorage bodyStorageSyntax
  exprStoragePreservation supportedStmts

Theorem eval_expr_body_oracle_storage:
  !tops cx e env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    well_typed_expr env e /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res, st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `EVERY (oracle_internal_call_storage cx) (int_calls_expr e)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qmatch_goalsub_rename_tac `oracle_internal_call_storage cx callee` >>
     `FST callee = NONE` by metis_tac[] >>
     PairCases_on `callee` >> gvs[] >>
     irule supported_main_callee_storage >> qexists_tac `tops` >> simp[]) >>
  fs[expr_has_evm_run_def] >>
  drule_all (cj 5 eval_expr_oracle_storage_results_mutual) >> simp[]
QED

Theorem eval_stmts_body_oracle_storage:
  (!tops bindings cx s env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' /\
     runtime_storage_consistent env cx st /\
     functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmt cx s st = (res, st') ==>
     contract_storage_well_formed cx st') /\
  (!tops bindings cx ss env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmts tops bindings ss /\ type_stmts env ret_ty ss = SOME env' /\
     runtime_storage_consistent env cx st /\
     functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmts cx ss st = (res, st') ==>
     contract_storage_well_formed cx st')
Proof
  conj_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac storage_stmt_syntax >>
  FIRST
    [`EVERY (oracle_internal_call_storage cx) (int_calls_stmt s)` by
       (fs[EVERY_MEM] >> rpt strip_tac >>
        irule supported_internal_callee_storage >> qexists_tac `tops` >>
        simp[] >> metis_tac[]) >>
     drule_all (cj 1 eval_stmts_oracle_storage_mutual) >> simp[],
     `EVERY (oracle_internal_call_storage cx) (int_calls_stmts ss)` by
       (fs[EVERY_MEM] >> rpt strip_tac >>
        irule supported_internal_callee_storage >> qexists_tac `tops` >>
        simp[] >> metis_tac[]) >>
     drule_all (cj 2 eval_stmts_oracle_storage_mutual) >> simp[]]
QED
