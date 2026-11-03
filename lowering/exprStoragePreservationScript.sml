(*
 * Storage well-formedness across an expression the lowering simulates
 *
 * vyperTypeEvalStoragePreservation's
 * eval_expr_preserves_contract_storage_well_formed assumes protected_storage_calls_preserve and
 * protected_storage_creates_preserve: postulates about the EVM code that
 * external calls, raw_call and the creates run.  The lowering's expressions
 * need neither.  They take external calls and send from the outcome oracle
 * (the source's outcomes are SOME, as state_rel has it), whose successful
 * outcomes keep storage well formed by oracle_storage_ok; they make no
 * internal calls (int_calls_expr e = []); and they have no raw_call or
 * create (expr_has_evm_run), the calls the source runs on the EVM even
 * with the oracle.
 *
 * TOP-LEVEL:
 *   eval_expr_oracle_preserves_contract_storage_well_formed
 *)

Theory exprStoragePreservation
Ancestors
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeExprSoundness vyperTypeCallStackSoundness vyperStorageLayoutSafety
  vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperCallOutcomeStorage
  vyperEvalOutcomeSuffix supportedExprTraverse exprOracleStoragePreservation

Theorem eval_expr_oracle_preserves_contract_storage_well_formed:
  !cx e env st res st'.
    well_typed_expr env e /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    int_calls_expr e = [] /\ call_evaluation_safe cx (int_calls_expr e) /\
    ~expr_has_evm_run e /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res, st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  gvs[expr_has_evm_run_def] >>
  `call_evaluation_safe cx (int_calls_expr e)` by simp[] >>
  drule_all (cj 5 eval_expr_oracle_storage_mutual) >> simp[]
QED
