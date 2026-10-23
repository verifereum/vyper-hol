Theory vyperAccountSupply
Ancestors
  vfmExecution vfmState pred_set arithmetic vyperTypeInvariants
Libs
  wordsLib

val _ = Parse.hide "from";

Definition accounts_supply_bounded_def:
  accounts_supply_bounded accounts <=>
    !s. FINITE s ==>
      SIGMA (\a. (lookup_account a accounts).balance) s < 2 ** 256
End

Theorem accounts_supply_balance:
  accounts_supply_bounded accounts ==>
  (lookup_account a accounts).balance < 2 ** 256
Proof
  rw[accounts_supply_bounded_def] >>
  first_x_assum (qspec_then `{a}` mp_tac) >> simp[SUM_IMAGE_SING]
QED

Theorem accounts_supply_pair:
  accounts_supply_bounded accounts /\ a <> b ==>
  (lookup_account a accounts).balance +
  (lookup_account b accounts).balance < 2 ** 256
Proof
  rw[accounts_supply_bounded_def] >>
  first_x_assum (qspec_then `{a;b}` mp_tac) >> simp[SUM_IMAGE_THM, DELETE_INSERT]
QED

Theorem accounts_supply_decrease:
  accounts_supply_bounded accounts /\
  (!a. (lookup_account a accounts').balance <=
       (lookup_account a accounts).balance) ==>
  accounts_supply_bounded accounts'
Proof
  rw[accounts_supply_bounded_def] >>
  `SIGMA (\a. (lookup_account a accounts').balance) s <=
   SIGMA (\a. (lookup_account a accounts).balance) s` by
    (irule SUM_IMAGE_MONO_LESS_EQ >> simp[]) >>
  first_x_assum (qspec_then `s` mp_tac) >> simp[]
QED

Theorem accounts_supply_empty:
  accounts_supply_bounded empty_accounts
Proof
  rw[accounts_supply_bounded_def] >>
  `SIGMA (\a. (lookup_account a empty_accounts).balance) s = 0` by
    simp[SUM_IMAGE_ZERO, lookup_account_def, empty_accounts_def,
         empty_account_state_def] >> simp[]
QED

Theorem accounts_supply_zero_balance:
  accounts_supply_bounded accounts ==>
  accounts_supply_bounded
    (update_account a (lookup_account a accounts with balance := 0) accounts)
Proof
  strip_tac >> irule accounts_supply_decrease >>
  qexists_tac `accounts` >> simp[] >> gen_tac >>
  simp[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  IF_CASES_TAC >> simp[lookup_account_def]
QED

Theorem account_sum_update:
  FINITE s /\ a IN s ==>
  SIGMA (\x. (lookup_account x (update_account a ac accounts)).balance) s =
    ac.balance + SIGMA (\x. (lookup_account x accounts).balance) (s DELETE a)
Proof
  strip_tac >>
  `s = a INSERT (s DELETE a)` by simp[] >>
  once_asm_rewrite_tac[] >> simp[SUM_IMAGE_THM, lookup_account_def, update_account_def] >>
  irule SUM_IMAGE_CONG >>
  simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem account_sum_transfer_closed:
  FINITE s /\ from IN s /\ to IN s /\
  n <= (lookup_account from accounts).balance ==>
  SIGMA (\x. (lookup_account x
    (vfmExecution$transfer_value from to n accounts)).balance) s =
  SIGMA (\x. (lookup_account x accounts).balance) s
Proof
  rw[vfmExecutionTheory.transfer_value_def] >> gvs[] >>
  simp[account_sum_update, SUM_IMAGE_DELETE] >>
  ` (lookup_account from accounts).balance <=
    SIGMA (\x. (lookup_account x accounts).balance) (s DELETE to)` by
      (qspecl_then [`\x. (lookup_account x accounts).balance`,
                     `s DELETE to`, `from`] mp_tac SUM_IMAGE_IN_LE >> simp[]) >>
  `(lookup_account to accounts).balance <=
    SIGMA (\x. (lookup_account x accounts).balance) s` by
      (qspecl_then [`\x. (lookup_account x accounts).balance`,
                     `s`, `to`] mp_tac SUM_IMAGE_IN_LE >> simp[]) >>
  gvs[SUM_IMAGE_DELETE] >> decide_tac
QED

Theorem accounts_supply_transfer:
  accounts_supply_bounded accounts /\
  n <= (lookup_account from accounts).balance ==>
  accounts_supply_bounded (vfmExecution$transfer_value from to n accounts)
Proof
  strip_tac >> rw[accounts_supply_bounded_def] >>
  qmatch_goalsub_abbrev_tac `SIGMA f s` >>
  `SIGMA f s <= SIGMA f (from INSERT to INSERT s)` by
    (irule SUM_IMAGE_SUBSET_LE >> simp[SUBSET_DEF]) >>
  `SIGMA f (from INSERT to INSERT s) =
   SIGMA (\x. (lookup_account x accounts).balance) (from INSERT to INSERT s)` by
    (simp[Abbr `f`] >> irule account_sum_transfer_closed >> simp[]) >>
  fs[accounts_supply_bounded_def] >>
  first_x_assum (qspec_then `from INSERT to INSERT s` mp_tac) >> simp[]
QED

Theorem accounts_supply_delete_account:
  accounts_supply_bounded accounts ==>
  accounts_supply_bounded (update_account a empty_account_state accounts)
Proof
  strip_tac >> irule accounts_supply_decrease >> qexists_tac `accounts` >>
  simp[] >> gen_tac >>
  simp[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  IF_CASES_TAC >> simp[empty_account_state_def]
QED

Theorem accounts_supply_process_deletions:
  !ds accounts. accounts_supply_bounded accounts ==>
  accounts_supply_bounded (vfmExecution$process_deletions ds accounts)
Proof
  Induct >> simp[vfmExecutionTheory.process_deletions_def,
                accounts_supply_delete_account]
QED

Theorem accounts_supply_transfer_well_typed:
  accounts_supply_bounded accounts /\ accounts_well_typed accounts /\
  n <= (lookup_account from accounts).balance ==>
  accounts_well_typed (vfmExecution$transfer_value from to n accounts)
Proof
  strip_tac >>
  drule_all accounts_supply_transfer >> disch_tac >>
  simp[accounts_well_typed_def, account_well_typed_def] >> gen_tac >>
  conj_tac >- (irule (SRULE [] accounts_supply_balance) >> simp[]) >>
  gvs[vfmExecutionTheory.transfer_value_def, accounts_well_typed_def,
      account_well_typed_def, lookup_account_def, update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  simp[combinTheory.UPDATE_def] >> rpt (IF_CASES_TAC >> gvs[])
QED

Theorem accounts_supply_selfdestruct_well_typed:
  accounts_supply_bounded accounts /\ accounts_well_typed accounts ==>
  accounts_well_typed
    (if created then
       let ac = vfmExecution$transfer_value self beneficiary
                  (lookup_account self accounts).balance accounts in
       update_account self (lookup_account self ac with balance := 0) ac
     else vfmExecution$transfer_value self beneficiary
                  (lookup_account self accounts).balance accounts)
Proof
  strip_tac >>
  `accounts_well_typed (vfmExecution$transfer_value self beneficiary
      (lookup_account self accounts).balance accounts)` by
    (irule accounts_supply_transfer_well_typed >> simp[]) >>
  Cases_on `created` >> simp[] >>
  gvs[accounts_well_typed_def, account_well_typed_def, lookup_account_def,
      update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  gen_tac >> IF_CASES_TAC >> gvs[]
QED

(* The old per-account domain admits this overflow witness.  The candidate
   supply domain deliberately excludes it; transfer itself remains unchecked. *)
Theorem accounts_supply_overflow_regression:
  let accounts = update_account (0w:address)
      (empty_account_state with balance := 1)
      (update_account (1w:address)
        (empty_account_state with balance := 2 ** 256 - 1) empty_accounts) in
  (lookup_account 1w (vfmExecution$transfer_value 0w 1w 1 accounts)).balance =
    2 ** 256 /\ ~accounts_supply_bounded accounts
Proof
  simp[] >> conj_tac >- EVAL_TAC >>
  strip_tac >> drule accounts_supply_pair >>
  disch_then (qspecl_then [`0w`, `1w`] mp_tac) >> EVAL_TAC
QED

Theorem accounts_supply_recipient_bound:
  accounts_supply_bounded accounts /\ from <> to /\
  n <= (lookup_account from accounts).balance ==>
  (lookup_account to accounts).balance + n < 2 ** 256
Proof
  strip_tac >> drule_all accounts_supply_pair >> simp[]
QED

val () = List.app (fn (n, th) =>
  print (n ^ ": " ^ PolyML.makestring (Tag.dest_tag (Thm.tag th)) ^ "\n"))
  (DB.thms "vyperAccountSupply");
