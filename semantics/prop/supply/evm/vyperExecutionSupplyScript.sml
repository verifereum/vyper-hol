(* TOP-LEVEL: account_supply_bound, execution_supply_bound and adapter initialization.
 *)
Theory vyperExecutionSupply
Ancestors
  vyperAccountSupply vyperSupplyBoundary vyperInterpreter vyperCreate
  vfmExecution vfmContext vfmState pred_set arithmetic list

(* Proof-only supply budget: snapshots are bounded individually. *)
Definition account_supply_bound_def:
  account_supply_bound budget accounts <=>
    !s. FINITE s ==>
      SIGMA (\a. (lookup_account a accounts).balance) s < budget
End

Definition execution_supply_bound_def:
  execution_supply_bound budget st <=>
    account_supply_bound budget st.rollback.accounts /\
    EVERY (\p. account_supply_bound budget (SND p).accounts) st.contexts
End

Theorem account_supply_bound_256:
  account_supply_bound (2 ** 256) accounts <=> accounts_supply_bounded accounts
Proof
  simp[account_supply_bound_def, accounts_supply_bounded_def]
QED

Theorem account_supply_bound_decrease:
  account_supply_bound budget accounts /\
  (!a. (lookup_account a accounts').balance <=
       (lookup_account a accounts).balance) ==>
  account_supply_bound budget accounts'
Proof
  rw[account_supply_bound_def] >>
  `SIGMA (\a. (lookup_account a accounts').balance) s <=
   SIGMA (\a. (lookup_account a accounts).balance) s` by
    (irule SUM_IMAGE_MONO_LESS_EQ >> simp[]) >>
  first_x_assum (qspec_then `s` mp_tac) >> simp[]
QED

Theorem account_supply_bound_transfer:
  account_supply_bound budget accounts /\
  n <= (lookup_account sender accounts).balance ==>
  account_supply_bound budget (vfmExecution$transfer_value sender recipient n accounts)
Proof
  strip_tac >> rw[account_supply_bound_def] >>
  qmatch_goalsub_abbrev_tac `SIGMA f s` >>
  `SIGMA f s <= SIGMA f (sender INSERT recipient INSERT s)` by
    (irule SUM_IMAGE_SUBSET_LE >> simp[SUBSET_DEF]) >>
  `SIGMA f (sender INSERT recipient INSERT s) =
   SIGMA (\x. (lookup_account x accounts).balance)
     (sender INSERT recipient INSERT s)` by
    (simp[Abbr `f`] >> irule account_sum_transfer_closed >> simp[]) >>
  fs[account_supply_bound_def] >>
  first_x_assum (qspec_then `sender INSERT recipient INSERT s` mp_tac) >> simp[]
QED

Theorem account_supply_bound_install:
  account_supply_bound budget accounts /\
  ac.balance <= (lookup_account a accounts).balance ==>
  account_supply_bound budget (update_account a ac accounts)
Proof
  strip_tac >> irule account_supply_bound_decrease >>
  qexists_tac `accounts` >> simp[] >> gen_tac >>
  simp[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  IF_CASES_TAC >> gvs[lookup_account_def]
QED

Theorem account_supply_bound_clear:
  account_supply_bound budget accounts ==>
  account_supply_bound budget (update_account a empty_account_state accounts)
Proof
  strip_tac >> irule account_supply_bound_install >>
  simp[empty_account_state_def]
QED

Theorem account_supply_bound_nonce:
  account_supply_bound budget accounts ==>
  account_supply_bound budget (vfmExecution$increment_nonce a accounts)
Proof
  simp[vfmExecutionTheory.increment_nonce_def] >> strip_tac >>
  irule account_supply_bound_install >> simp[]
QED

Theorem account_supply_bound_create_prelude:
  account_supply_bound budget accounts /\
  value <= (lookup_account sender accounts).balance ==>
  account_supply_bound budget (create_prelude_accounts sender address value accounts)
Proof
  simp[create_prelude_accounts_def] >> strip_tac >>
  `account_supply_bound budget
     (vfmExecution$increment_nonce address
       (vfmExecution$increment_nonce sender accounts))` by
    simp[account_supply_bound_nonce] >>
  irule account_supply_bound_transfer >> simp[] >>
  gvs[vfmExecutionTheory.increment_nonce_def, lookup_account_def,
      update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt (IF_CASES_TAC >> gvs[])
QED

Theorem make_ext_call_state_supply:
  account_supply_bound budget accounts /\
  ext_call_value_transfer_ok caller callee value_opt accounts ==>
  execution_supply_bound budget
    (make_ext_call_state caller callee code calldata value_opt accounts ts txp)
Proof
  Cases_on `value_opt` >>
  simp[make_ext_call_state_def, execution_supply_bound_def,
       ext_call_value_transfer_ok_def] >> strip_tac >>
  irule account_supply_bound_transfer >> simp[]
QED

Theorem make_delegate_call_state_supply:
  account_supply_bound budget accounts ==>
  execution_supply_bound budget
    (make_delegate_call_state cx target data accounts ts)
Proof
  simp[make_delegate_call_state_def] >>
  pairarg_tac >> simp[execution_supply_bound_def]
QED

Theorem make_create_state_supply:
  account_supply_bound budget accounts ==>
  execution_supply_bound budget
    (make_create_state sender address initcode value accounts ts pending txp)
Proof
  simp[make_create_state_def, execution_supply_bound_def,
       account_supply_bound_clear]
QED

Theorem make_funded_create_state_supply:
  account_supply_bound budget accounts /\
  value <= (lookup_account sender accounts).balance ==>
  execution_supply_bound budget
    (make_create_state sender address initcode value
      (create_prelude_accounts sender address value accounts) ts pending txp)
Proof
  strip_tac >> irule make_create_state_supply >>
  irule account_supply_bound_create_prelude >> simp[]
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperExecutionSupply");
