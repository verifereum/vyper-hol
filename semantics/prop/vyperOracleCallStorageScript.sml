(* Storage well-formedness across external calls in oracle mode
   (IS_SOME st.outcomes). There eval_send and eval_ext_call adopt the
   recorded call outcome instead of running the callee through
   run_ext_call, so these lemmas need no hypothesis about what the callee's
   code does to our storage (protected_storage_calls_preserve), which the
   non-oracle versions in vyperTypeEvalStoragePreservation need. *)
Theory vyperOracleCallStorage
Ancestors
  vyperInterpreter vyperCallOutcomeStorage vyperTypeEvalStoragePreservation
  vyperStorageLayoutSafety vyperCallOutcome vyperState vyperMisc
Libs monadsyntax

Theorem eval_send_oracle_storage_preserved:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  IS_SOME st.outcomes /\
  eval_send cx has_gas vs st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  Cases_on `st.outcomes` >> simp[] >>
  Cases_on `vs` >- (simp[eval_send_def, raise_def] >> rw[] >> gvs[]) >>
  Cases_on `t` >- (simp[eval_send_def, raise_def] >> rw[] >> gvs[]) >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       check_def, lift_option_type_def, lift_option_def, return_def, raise_def,
       COND_RATOR, vfmTypesTheory.option_CASE_rator,
       vfmTypesTheory.prod_CASE_rator, vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, assert_def, adopt_call_outcome_INR_storage] >>
  metis_tac[take_call_outcome_storage_suffix,
            take_adopt_call_outcome_storage_suffix]
QED

Theorem eval_ext_call_effects_oracle_storage_preserved:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  IS_SOME st.outcomes /\
  eval_ext_call_effects cx target calldata value_opt gas accounts st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  Cases_on `st.outcomes` >> simp[] >>
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def,
       return_def, raise_def, COND_RATOR, vfmTypesTheory.option_CASE_rator,
       vfmTypesTheory.prod_CASE_rator, vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, adopt_call_outcome_INR_storage] >>
  metis_tac[take_call_outcome_storage_suffix,
            take_adopt_call_outcome_storage_suffix]
QED

Theorem eval_ext_call_oracle_storage_preserved:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  IS_SOME st.outcomes /\
  eval_ext_call cx static skip_check sig opts vs st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  PairCases_on `sig` >>
  Cases_on `vs` >- (simp[eval_ext_call_def, raise_def] >> rw[] >> gvs[]) >>
  simp[eval_ext_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, check_def, lift_option_type_def, lift_option_def,
       lift_sum_runtime_def, get_accounts_def, return_def, raise_def,
       COND_RATOR, vfmTypesTheory.option_CASE_rator,
       vfmTypesTheory.prod_CASE_rator, vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all eval_ext_call_effects_oracle_storage_preserved >> simp[]
QED
