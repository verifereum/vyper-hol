(* TOP-LEVEL: source_supply_action_create for funded creation and rollback.
 *)
Theory vyperSourceCreateSupply
Ancestors
  list pair option arithmetic vyperMisc vyperSourceSupplyDefs
  vyperSupplyBoundary vyperAdapterSupply vyperCreate vyperState vyperCallOutcome
Libs
  proofAuditLib
  pairLib

Theorem source_supply_action_create_oracle_result[local]:
  source_supply_action (create_oracle_result salt value initcode rof)
Proof
  simp[source_supply_action_def] >> qx_gen_tac `before` >> strip_tac >>
  simp[create_oracle_result_def] >>
  qmatch_goalsub_abbrev_tac `take_create_outcome kind value initcode before` >>
  Cases_on `take_create_outcome kind value initcode before` >>
  rename1 `_ = (res, mid)` >>
  Cases_on `res` >> simp[]
  >- (PairCases_on `x` >> drule take_create_outcome_success >> strip_tac >>
      `accounts_supply_bounded x0.cr_accounts /\ supply_safe_outcomes os` by
        gvs[create_outcome_request_def, source_supply_def] >>
      drule_all supply_safe_take_outcome_bounded >> strip_tac >>
      rw[] >> gvs[adopt_call_outcome_equation] >> rw[] >>
      gvs[source_supply_def]) >>
  drule take_create_outcome_frame >> strip_tac >>
  Cases_on `before.outcomes`
  >- gvs[take_create_outcome_def] >>
  drule_all take_create_outcome_suffix >> strip_tac >>
  gvs[source_supply_def, supply_safe_outcomes_def, EVERY_APPEND,
      evaluation_state_component_equality]
QED

Theorem create_oracle_result_supply[local]:
  accounts_supply_bounded st.accounts /\
  (!os. st.outcomes = SOME os ==> supply_safe_outcomes os) ==>
  accounts_supply_bounded (SND (create_oracle_result salt value initcode rof st)).accounts /\
  (!os. (SND (create_oracle_result salt value initcode rof st)).outcomes = SOME os ==>
        supply_safe_outcomes os)
Proof
  strip_tac >>
  `source_supply (SND (create_oracle_result salt value initcode rof st))` by
    (irule (REWRITE_RULE [source_supply_action_def]
              source_supply_action_create_oracle_result) >>
     simp[source_supply_def]) >>
  gvs[source_supply_def]
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
        NOT_LESS, AllCaseEqs()]) >>
  TRY (irule create_oracle_result_supply >> simp[] >> NO_TAC) >>
  drule_all (SRULE [] run_create_evm_supply) >> simp[]
QED

val () = proofAuditLib.check_theory "vyperSourceCreateSupply";
