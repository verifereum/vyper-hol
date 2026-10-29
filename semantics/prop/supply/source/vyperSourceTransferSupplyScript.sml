(* TOP-LEVEL: source transfer and unchecked selfdestruct-effect supply preservation.
 *)
Theory vyperSourceTransferSupply
Ancestors
  list pair arithmetic vyperSourceSupplyDefs vyperAccountSupply
  vyperSupplyBoundary vyperSourcePrimitiveSupply vyperInterpreter vyperState
Libs
  monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

(* The checked source transfer writes the two distinct accounts in the
   opposite order from Verifereum; commute those writes before reusing its
   conservation theorem. *)
Theorem source_transfer_accounts_supply:
  accounts_supply_bounded accounts /\ sender <> recipient /\
  amount <= (lookup_account sender accounts).balance ==>
  accounts_supply_bounded
    (update_account sender
       (lookup_account sender accounts with balance updated_by flip $- amount)
       (update_account recipient
         (lookup_account recipient accounts with balance updated_by $+ amount) accounts))
Proof
  strip_tac >> Cases_on `amount = 0`
  >- (irule accounts_supply_decrease >> qexists_tac `accounts` >> simp[] >>
      gen_tac >>
      simp[vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
           combinTheory.C_DEF, combinTheory.UPDATE_def] >>
      rpt (COND_CASES_TAC >> gvs[])) >>
  `update_account sender
     (lookup_account sender accounts with balance updated_by flip $- amount)
     (update_account recipient
       (lookup_account recipient accounts with balance updated_by $+ amount) accounts) =
   vfmExecution$transfer_value sender recipient amount accounts` by
    simp[vfmExecutionTheory.transfer_value_def, vfmStateTheory.update_account_def,
         combinTheory.UPDATE_COMMUTES] >>
  pop_assum SUBST1_TAC >> irule accounts_supply_transfer >> simp[]
QED

Theorem source_supply_action_transfer:
  source_supply_action (vyperInterpreter$transfer_value sender recipient amount)
Proof
  simp[source_supply_action_def] >> qx_gen_tac `before` >> strip_tac >>
  Cases_on `amount = 0 \/ sender = recipient`
  >- gvs[vyperInterpreterTheory.transfer_value_def, return_def] >>
  gvs[vyperInterpreterTheory.transfer_value_def, get_accounts_def,
      check_def, assert_def, update_accounts_def, bind_def, ignore_bind_def,
      return_def, raise_def, combinTheory.o_DEF, COND_RATOR,
      source_supply_def, AllCaseEqs()] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >>
  irule (SRULE [] source_transfer_accounts_supply) >> simp[]
QED

Theorem source_supply_action_send_call_value:
  source_supply_action (send_call_value mut cx)
Proof
  Cases_on `cx.txn.value = 0` >>
  simp[send_call_value_def, source_supply_action_return] >>
  irule source_supply_action_ignore_bind >>
  simp[source_supply_reads, source_supply_action_transfer]
QED

Theorem source_supply_get_accounts_result:
  source_supply before /\ get_accounts before = (INL accounts,post) ==>
  accounts_supply_bounded accounts
Proof
  rw[get_accounts_def, return_def, source_supply_def] >> gvs[]
QED

Theorem lift_option_success:
  lift_option value message before = (INL result,post) ==>
  value = SOME result
Proof
  Cases_on `value` >> simp[lift_option_def, return_def, raise_def]
QED

(* The full-balance read and unchecked transfer form one operation: the
   captured amount is affordable in this exact input account map. *)
Theorem source_supply_action_selfdestruct_effect:
  source_supply_action
    (do
       accounts <- get_accounts;
       update_accounts (vfmExecution$transfer_value self beneficiary
         (lookup_account self accounts).balance);
       if created then do
         update_accounts (\accounts. update_account self
           (lookup_account self accounts with balance := 0) accounts);
         update_pending_deletions (CONS self)
       od else return ();
       vyperState$raise error
     od)
Proof
  simp[source_supply_action_def] >> qx_gen_tac `before` >> strip_tac >>
  `accounts_supply_bounded (vfmExecution$transfer_value self beneficiary
      (lookup_account self before.accounts).balance before.accounts)` by
    (irule accounts_supply_transfer >> fs[source_supply_def]) >>
  Cases_on `created` >>
  gvs[get_accounts_def, update_accounts_def, update_pending_deletions_def,
      bind_def, ignore_bind_def, return_def, raise_def,
      source_supply_def, evaluation_state_accfupds,
      accounts_supply_zero_balance]
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperSourceTransferSupply");
