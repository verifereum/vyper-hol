(* TOP-LEVEL: source_supply_action_create for funded creation and rollback.
 *)
Theory vyperSourceCreateSupply
Ancestors
  list pair option arithmetic vyperMisc vyperSourceSupplyDefs
  vyperSupplyBoundary vyperAdapterSupply vyperCreate vyperState
  vyperCallOutcome extCallOracle
Libs
  pairLib

Theorem source_supply_action_create_oracle_result[local]:
  source_supply_action (create_oracle_result salt value initcode rof)
Proof
  simp[source_supply_action_def] >> qx_gen_tac `before` >> strip_tac >>
  Cases_on `before.outcomes`
  >- simp[create_oracle_result_def, take_create_outcome_def] >>
  rename1 `before.outcomes = SOME os` >>
  `accounts_supply_bounded before.accounts /\ supply_safe_outcomes os` by
    fs[source_supply_def] >>
  simp[create_oracle_result_def, take_create_outcome_def] >>
  pairarg_tac >>
  `accounts_supply_bounded
     (create_outcome_request
       (case salt of NONE => CreateCall | SOME s => Create2Call s)
       value initcode before).cr_accounts` by simp[create_outcome_request_def] >>
  drule_all supply_safe_take_outcome >> strip_tac >>
  Cases_on `salt` >> Cases_on `outcome.co_success` >>
  Cases_on `outcome.co_created = 0w` >> Cases_on `rof` >>
  rw[adopt_call_outcome_equation, create_outcome_request_def,
     source_supply_def, evaluation_state_accfupds] >>
  gvs[source_supply_def, evaluation_state_accfupds, AllCaseEqs()]
QED

(* Account replacement after the EVM run uses the adapter's proved bound;
   the temporary funded prelude is never used as a fresh funding premise. *)
Theorem source_supply_action_create:
  source_supply_action (eval_create cx kind has_salt rof arg_tys values blueprint_size)
Proof
  simp[source_supply_action_def] >> qx_gen_tac `before` >> strip_tac >>
  `accounts_supply_bounded before.accounts` by fs[source_supply_def] >>
  simp_tac bool_ss [eval_create_def, LET_THM, bind_def, ignore_bind_def,
    get_accounts_def, get_transient_storage_def, get_pending_deletions_def,
    lift_option_type_def, check_def, assert_def, update_accounts_def,
    update_transient_def, update_pending_deletions_def, append_logs_def,
    create_soft_failure_def, return_def, raise_def, option_CASE_rator,
    prod_CASE_rator, COND_RATOR] >>
  rpt (BasicProvers.PURE_TOP_CASE_TAC >>
    gvs[return_def, raise_def, source_supply_def, evaluation_state_accfupds,
        accounts_supply_increment_nonce, accounts_supply_create_rollback,
        NOT_LESS, AllCaseEqs()])
  >- (pure_rewrite_tac[GSYM source_supply_def] >>
      irule (SRULE [source_supply_action_def] source_supply_action_create_oracle_result) >>
      simp[source_supply_def]) >>
  drule_all (SRULE [] run_create_evm_supply) >> simp[]
QED
