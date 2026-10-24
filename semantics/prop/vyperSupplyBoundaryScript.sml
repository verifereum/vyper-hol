Theory vyperSupplyBoundary
Ancestors
  vyperAccountSupply vyperCallOutcome vyperCreate extCallOracle vfmState
  vfmExecution pred_set arithmetic vyperInterpreter

(* Proof-only contracts. Neither predicate changes runtime acceptance. *)
Definition supply_safe_outcome_def:
  supply_safe_outcome outcome <=>
    (outcome.co_success ==> accounts_supply_bounded outcome.co_accounts)
End

Definition supply_safe_outcomes_def:
  supply_safe_outcomes os <=> EVERY supply_safe_outcome os
End

Theorem supply_safe_take_outcome:
  accounts_supply_bounded rq.cr_accounts /\ supply_safe_outcomes os /\
  take_outcome rq os = (outcome, rest) ==>
  supply_safe_outcomes rest /\
  (outcome.co_success /\ ~rq.cr_static ==>
   accounts_supply_bounded outcome.co_accounts)
Proof
  rw[take_outcome_def] >>
  gvs[AllCaseEqs(), failed_outcome_def, supply_safe_outcomes_def,
      supply_safe_outcome_def]
QED

Theorem supply_safe_adopt:
  accounts_supply_bounded st.accounts /\
  (outcome.co_success /\ ~rq.cr_static ==>
    accounts_supply_bounded outcome.co_accounts) /\
  adopt_call_outcome rq outcome st = (res,st') ==>
  accounts_supply_bounded st'.accounts
Proof
  rw[adopt_call_outcome_equation] >> gvs[]
QED

Theorem supply_safe_take_adopt:
  accounts_supply_bounded st.accounts /\
  st.outcomes = SOME os /\ supply_safe_outcomes os /\
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st') /\
  adopt_call_outcome rq outcome st' = (res,st'') ==>
  accounts_supply_bounded st''.accounts /\
  ?rest. st''.outcomes = SOME rest /\ supply_safe_outcomes rest
Proof
  strip_tac >> drule take_call_outcome_success >> strip_tac >> gvs[] >>
  `accounts_supply_bounded
     (call_outcome_request target calldata value_opt st).cr_accounts` by
    simp[call_outcome_request_def] >>
  drule_all supply_safe_take_outcome >> strip_tac >>
  gvs[adopt_call_outcome_equation, call_outcome_request_def] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem accounts_supply_install_same_balance:
  accounts_supply_bounded accounts /\
  ac.balance = (lookup_account a accounts).balance ==>
  accounts_supply_bounded (update_account a ac accounts)
Proof
  strip_tac >> irule accounts_supply_decrease >> qexists_tac `accounts` >>
  simp[] >> gen_tac >>
  simp[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  IF_CASES_TAC >> gvs[lookup_account_def]
QED

Theorem accounts_supply_increment_nonce:
  accounts_supply_bounded accounts ==>
  accounts_supply_bounded (vfmExecution$increment_nonce a accounts)
Proof
  simp[vfmExecutionTheory.increment_nonce_def] >> strip_tac >>
  irule accounts_supply_install_same_balance >> simp[]
QED

Theorem accounts_supply_create_prelude:
  accounts_supply_bounded accounts /\
  value <= (lookup_account sender accounts).balance ==>
  accounts_supply_bounded (create_prelude_accounts sender address value accounts)
Proof
  simp[create_prelude_accounts_def] >> strip_tac >>
  irule accounts_supply_transfer >> conj_tac
  >- (irule accounts_supply_increment_nonce >>
      irule accounts_supply_increment_nonce >> simp[]) >>
  gvs[vfmExecutionTheory.increment_nonce_def, lookup_account_def,
      update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt (IF_CASES_TAC >> gvs[])
QED

Theorem accounts_supply_create_rollback:
  accounts_supply_bounded accounts ==>
  accounts_supply_bounded (create_rollback_accounts sender accounts)
Proof
  simp[create_rollback_accounts_def, accounts_supply_increment_nonce]
QED

(* The success premise below is deliberately explicit: the current EVM
   runtime account gate checks individual bounds, not conserved supply. *)
Theorem extract_call_result_supply_conditional:
  accounts_supply_bounded accounts /\
  (result = INR NONE ==> accounts_supply_bounded final_state.rollback.accounts) /\
  extract_call_result accounts ts (result,final_state) =
    SOME (success, data, accounts', ts', logs, deletions) ==>
  accounts_supply_bounded accounts'
Proof
  simp[extract_call_result_def] >>
  Cases_on `final_state.contexts` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `h` >>
  Cases_on `result` >> simp[] >> Cases_on `y` >> simp[] >>
  rw[] >> gvs[AllCaseEqs()]
QED

Theorem extract_create_result_supply_conditional:
  accounts_supply_bounded accounts /\
  (result = INR NONE ==> accounts_supply_bounded final_state.rollback.accounts) /\
  extract_create_result accounts ts pending (result,final_state) =
    SOME (code, accounts', ts', logs, data, pending') ==>
  accounts_supply_bounded accounts'
Proof
  simp[extract_create_result_def] >>
  Cases_on `final_state.contexts` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `h` >>
  Cases_on `result` >> simp[] >> Cases_on `y` >> simp[] >>
  rw[] >> gvs[AllCaseEqs()]
QED

Theorem finalize_pending_deletions_supply:
  accounts_supply_bounded am.accounts ==>
  accounts_supply_bounded (finalize_pending_deletions am).accounts
Proof
  simp[finalize_pending_deletions_def, accounts_supply_process_deletions]
QED

Theorem accounts_supply_finite_funding:
  FINITE funded /\
  (!a. a NOTIN funded ==> (lookup_account a accounts).balance = 0) /\
  SIGMA (\a. (lookup_account a accounts).balance) funded < 2 ** 256 ==>
  accounts_supply_bounded accounts
Proof
  strip_tac >> rw[accounts_supply_bounded_def] >>
  `SIGMA (\a. (lookup_account a accounts).balance) s =
   SIGMA (\a. (lookup_account a accounts).balance) (s INTER funded)` by
    (`s = (s INTER funded) UNION (s DIFF funded)` by SET_TAC[] >>
     `SIGMA (\a. (lookup_account a accounts).balance) (s DIFF funded) = 0` by
       (simp[SUM_IMAGE_ZERO] >> metis_tac[IN_DIFF]) >>
     qspecl_then [`s INTER funded`, `s DIFF funded`] mp_tac SUM_IMAGE_DISJOINT >>
     impl_tac >- (simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
     disch_then (qspec_then `\a. (lookup_account a accounts).balance` mp_tac) >>
     metis_tac[ADD_0]) >>
  `SIGMA (\a. (lookup_account a accounts).balance) (s INTER funded) <=
   SIGMA (\a. (lookup_account a accounts).balance) funded` by
    (irule SUM_IMAGE_SUBSET_LE >> simp[INTER_SUBSET]) >> gvs[]
QED

val () = List.app (fn (n, th) =>
  print (n ^ ": " ^ PolyML.makestring (Tag.dest_tag (Thm.tag th)) ^ "\n"))
  (DB.thms "vyperSupplyBoundary");
