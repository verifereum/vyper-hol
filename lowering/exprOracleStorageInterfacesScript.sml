(* Recursive-entry interfaces for postulate-free oracle evaluation. *)
Theory exprOracleStorageInterfaces
Ancestors
  supportedExprTraverse vyperTypeCallGraph vyperCallOutcomeStorage
  vyperEvalOutcomeSuffix
  vyperTypeEvalStoragePreservation vyperOracleCallStorage

Theorem supported_exprs_exists_not_every:
  ~supported_exprs_exists p es <=> EVERY (\e. ~supported_expr_exists p e) es
Proof
  Induct_on `es` >> simp[supported_expr_exists_def]
QED

Theorem supported_fields_exists_not_every:
  ~supported_fields_exists p fields <=>
  EVERY (\e. ~supported_expr_exists p e) (MAP SND fields)
Proof
  Induct_on `fields` >> simp[supported_expr_exists_def] >>
  Cases_on `h` >> simp[supported_expr_exists_def]
QED

Theorem int_calls_exprs_empty_every:
  int_calls_exprs es = [] <=> EVERY (\e. int_calls_expr e = []) es
Proof
  Induct_on `es` >> simp[int_calls_expr_def]
QED

Theorem int_calls_named_exprs_empty_every:
  int_calls_named_exprs fields = [] <=>
  EVERY (\e. int_calls_expr e = []) (MAP SND fields)
Proof
  Induct_on `fields` >> simp[int_calls_expr_def] >>
  Cases_on `h` >> simp[int_calls_expr_def]
QED

Theorem outcome_suffix_IS_SOME:
  outcome_suffix before after /\ IS_SOME before ==> IS_SOME after
Proof
  Cases_on `before` >> Cases_on `after` >>
  simp[outcome_suffix_def]
QED

Theorem oracle_storage_entry_suffix:
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  outcome_suffix st.outcomes st'.outcomes ==>
  IS_SOME st'.outcomes /\ oracle_storage_ok cx st'
Proof
  metis_tac[outcome_suffix_IS_SOME, oracle_storage_ok_suffix]
QED

(* A call or staticcall raw_call in oracle mode, given that its operands keep
   storage well formed: for the expression and body inductions. *)
Theorem eval_raw_call_expr_oracle_storage:
  contract_storage_well_formed cx st /\ IS_SOME st.outcomes /\
  oracle_storage_ok cx st /\ ~flags.rcf_is_delegate /\
  (!r s. eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (Call ty (RawCallTarget flags) es extra) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once vyperInterpreterTheory.evaluate_def,
                       vyperStateTheory.bind_def,
                       vyperStateTheory.ignore_bind_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by
    (first_x_assum (qspecl_then [`args_res`, `args_st`] mp_tac) >> simp[]) >>
  `IS_SOME args_st.outcomes /\ oracle_storage_ok cx args_st` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `args_res` >> simp[] >>
  simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.lift_option_type_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vfmTypesTheory.option_CASE_rator,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_at (Pat `eval_raw_call _ _ _ _ _ _ _ = _`)
    eval_raw_call_oracle_storage_preserved >> gvs[]
QED

Theorem eval_raw_call_calldata_expr_oracle_storage:
  contract_storage_well_formed cx st /\ IS_SOME st.outcomes /\
  oracle_storage_ok cx st /\ ~flags.rcf_is_delegate /\
  (!r s. eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (Call ty (RawCallCalldataTarget flags) es extra) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once vyperInterpreterTheory.evaluate_def,
                       vyperStateTheory.bind_def,
                       vyperStateTheory.ignore_bind_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by
    (first_x_assum (qspecl_then [`args_res`, `args_st`] mp_tac) >> simp[]) >>
  `IS_SOME args_st.outcomes /\ oracle_storage_ok cx args_st` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `args_res` >> simp[] >>
  simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.lift_option_type_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vfmTypesTheory.option_CASE_rator,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_at (Pat `eval_raw_call _ _ _ _ _ _ _ = _`)
    eval_raw_call_oracle_storage_preserved >> gvs[]
QED
