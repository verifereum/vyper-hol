(* Recursive-entry interfaces for postulate-free oracle evaluation. *)
Theory exprOracleStorageInterfaces
Ancestors
  supportedExprTraverse vyperTypeCallGraph vyperCallOutcomeStorage
  vyperEvalOutcomeSuffix
  vyperTypeEvalStoragePreservation

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
