(* TOP-LEVEL: proceed_call_supply and proceed_create_supply.
 * Helpers: saved-map, context, nonce, restoration and deletion boundaries.
 *)
Theory vyperPrimitiveSupply
Ancestors
  vyperExecutionSupply vyperPrecompileSupply
  vfmExecution vfmContext vfmState list rich_list

(* Local mutation boundaries for the run_call supply invariant. *)
Theorem execution_supply_live:
  execution_supply_bound budget st ==>
  account_supply_bound budget st.rollback.accounts
Proof
  simp[execution_supply_bound_def]
QED

Theorem execution_supply_saved:
  execution_supply_bound budget st /\ MEM (ctxt,rb) st.contexts ==>
  account_supply_bound budget rb.accounts
Proof
  simp[execution_supply_bound_def, EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `(ctxt,rb)` mp_tac) >> simp[]
QED

Theorem execution_supply_push:
  execution_supply_bound budget st /\ account_supply_bound budget rb.accounts ==>
  execution_supply_bound budget (SND (push_context (ctxt,rb) st))
Proof
  simp[push_context_def, vfmExecutionTheory.return_def, execution_supply_bound_def]
QED

Theorem execution_supply_pop:
  execution_supply_bound budget st ==>
  execution_supply_bound budget (SND (pop_context st))
Proof
  Cases_on `st.contexts` >>
  simp[pop_context_def, vfmExecutionTheory.return_def, fail_def,
       execution_supply_bound_def]
QED

Theorem execution_supply_restore:
  execution_supply_bound budget st /\ MEM (ctxt,rb) st.contexts ==>
  execution_supply_bound budget
    (SND (set_rollback rb (SND (pop_context st))))
Proof
  strip_tac >> drule_all execution_supply_saved >> strip_tac >>
  drule execution_supply_pop >>
  simp[set_rollback_def, vfmExecutionTheory.return_def, execution_supply_bound_def]
QED

Theorem execution_supply_current_context:
  execution_supply_bound budget st ==>
  execution_supply_bound budget (SND (set_current_context ctxt st))
Proof
  Cases_on `st.contexts` >>
  simp[set_current_context_def, vfmExecutionTheory.return_def, fail_def,
       execution_supply_bound_def]
QED

Theorem bounded_set_last_accounts:
  contexts <> [] /\
  EVERY (\p. account_supply_bound budget (SND p).accounts) contexts /\
  account_supply_bound budget accounts ==>
  EVERY (\p. account_supply_bound budget (SND p).accounts)
    (set_last_accounts accounts contexts)
Proof
  simp[set_last_accounts_def, EVERY_SNOC] >> strip_tac >>
  fs[EVERY_MEM] >> gen_tac >> strip_tac >> first_x_assum irule >>
  drule_all MEM_FRONT_NOT_NIL >> simp[]
QED

Theorem execution_supply_original:
  execution_supply_bound budget st /\ account_supply_bound budget accounts ==>
  execution_supply_bound budget (SND (set_original accounts st))
Proof
  simp[set_original_def] >> IF_CASES_TAC >>
  simp[fail_def, vfmExecutionTheory.return_def, execution_supply_bound_def,
       bounded_set_last_accounts]
QED

Theorem execution_supply_update_accounts:
  execution_supply_bound budget st /\
  account_supply_bound budget (f st.rollback.accounts) ==>
  execution_supply_bound budget (SND (vfmExecution$update_accounts f st))
Proof
  simp[vfmExecutionTheory.update_accounts_def, vfmExecutionTheory.return_def,
       execution_supply_bound_def]
QED

Theorem execution_supply_selfdestruct_accounts:
  execution_supply_bound budget st ==>
  execution_supply_bound budget
    (st with rollback updated_by (\rb. rb with accounts :=
      if created then
        update_account self (lookup_account self st.rollback.accounts with balance := 0)
          (vfmExecution$transfer_value self beneficiary
            (lookup_account self st.rollback.accounts).balance st.rollback.accounts)
      else vfmExecution$transfer_value self beneficiary
        (lookup_account self st.rollback.accounts).balance st.rollback.accounts))
Proof
  strip_tac >>
  `account_supply_bound budget
     (vfmExecution$transfer_value self beneficiary
       (lookup_account self st.rollback.accounts).balance st.rollback.accounts)` by
    (irule account_supply_bound_transfer >>
     gvs[execution_supply_bound_def]) >>
  simp[execution_supply_bound_def] >> conj_tac
  >- (Cases_on `created` >> simp[] >>
      irule account_supply_bound_install >> simp[]) >>
  gvs[execution_supply_bound_def]
QED

Theorem proceed_call_supply_nonprecompile:
  execution_supply_bound budget st /\
  value <= (lookup_account sender st.rollback.accounts).balance /\
  ~fIN address precompile_addresses ==>
  execution_supply_bound budget
    (SND (proceed_call op sender address value argsOffset argsSize code stipend
            outputTo st))
Proof
  strip_tac >> Cases_on `st.contexts` >>
  gvs[proceed_call_def, get_rollback_def, read_memory_def,
      get_current_context_def, get_caller_def, get_value_def, get_static_def,
      push_context_def, vfmExecutionTheory.update_accounts_def,
      vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
      vfmExecutionTheory.ignore_bind_def, fail_def] >>
  IF_CASES_TAC >>
  gvs[vfmExecutionTheory.update_accounts_def, get_current_context_def,
      push_context_def, vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
      vfmExecutionTheory.ignore_bind_def, execution_supply_bound_def] >>
  irule account_supply_bound_transfer >> simp[]
QED

Theorem execution_supply_last:
  execution_supply_bound budget st /\ st.contexts <> [] ==>
  account_supply_bound budget (SND (LAST st.contexts)).accounts
Proof
  simp[execution_supply_bound_def, EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `LAST st.contexts` mp_tac) >> simp[MEM_LAST_NOT_NIL]
QED

Theorem proceed_call_supply:
  execution_supply_bound budget st /\
  value <= (lookup_account sender st.rollback.accounts).balance ==>
  execution_supply_bound budget
    (SND (proceed_call op sender address value argsOffset argsSize code stipend
            outputTo st))
Proof
  strip_tac >> Cases_on `fIN address precompile_addresses`
  >| [ALL_TAC, irule proceed_call_supply_nonprecompile >> simp[]] >>
  Cases_on `st.contexts` >>
  gvs[proceed_call_def, get_rollback_def, read_memory_def,
      get_current_context_def, get_caller_def, get_value_def, get_static_def,
      push_context_def, vfmExecutionTheory.update_accounts_def,
      vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
      vfmExecutionTheory.ignore_bind_def, fail_def] >>
  IF_CASES_TAC >>
  gvs[vfmExecutionTheory.update_accounts_def, get_current_context_def,
      push_context_def, vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
      vfmExecutionTheory.ignore_bind_def] >>
  irule dispatch_precompiles_supply >>
  gvs[execution_supply_bound_def] >>
  irule account_supply_bound_transfer >> simp[]
QED

Theorem proceed_create_supply:
  execution_supply_bound budget st /\
  value <= (lookup_account sender st.rollback.accounts).balance ==>
  execution_supply_bound budget
    (SND (proceed_create sender address value code cappedGas st))
Proof
  strip_tac >>
  `account_supply_bound budget
     (vfmExecution$increment_nonce address
       (vfmExecution$increment_nonce sender st.rollback.accounts))` by
    gvs[execution_supply_bound_def, account_supply_bound_nonce] >>
  `account_supply_bound budget
     (vfmExecution$transfer_value sender address value
       (vfmExecution$increment_nonce address
         (vfmExecution$increment_nonce sender st.rollback.accounts)))` by
    (irule account_supply_bound_transfer >> simp[] >>
     gvs[vfmExecutionTheory.increment_nonce_def, lookup_account_def,
         update_account_def, combinTheory.APPLY_UPDATE_THM] >>
     rpt (IF_CASES_TAC >> gvs[])) >>
  Cases_on `st.contexts = []`
  >- gvs[proceed_create_def, vfmExecutionTheory.update_accounts_def,
         get_rollback_def, get_original_def, fail_def,
         vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
         vfmExecutionTheory.ignore_bind_def, execution_supply_bound_def,
         account_supply_bound_nonce] >>
  drule_all execution_supply_last >> strip_tac >>
  gvs[proceed_create_def, vfmExecutionTheory.update_accounts_def,
      get_rollback_def, get_original_def, set_original_def, push_context_def,
      vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
      vfmExecutionTheory.ignore_bind_def, execution_supply_bound_def,
      bounded_set_last_accounts, account_supply_bound_clear,
      account_supply_bound_nonce]
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperPrimitiveSupply");
