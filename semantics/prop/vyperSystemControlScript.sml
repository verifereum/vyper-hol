(* Raw revert data, selfdestruct account effects and terminal control. *)
Theory vyperSystemControl
Ancestors
  vyperInterpreter vyperSmallStep[ignore_grammar] vyperState vyperAST
  vyperMisc vyperTypeSystem vyperValue vyperValueOperation vfmExecution vfmState list
Libs BasicProvers

Theorem raw_revert_no_success:
  eval_expr cx (Call ty RawRevert es drv) st <> (INL value,st')
Proof
  simp[Once evaluate_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.raise_def] >>
  rpt (PURE_TOP_CASE_TAC >>
       simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
            vyperStateTheory.lift_option_type_def, vyperStateTheory.return_def, vyperStateTheory.raise_def])
QED

Theorem selfdestruct_no_success:
  eval_expr cx (Call ty SelfDestructTarget es drv) st <> (INL value,st')
Proof
  simp[Once evaluate_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.raise_def] >>
  rpt (PURE_TOP_CASE_TAC >>
       simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
            vyperStateTheory.lift_option_type_def, vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
            vyperStateTheory.update_pending_deletions_def, vyperStateTheory.return_def, vyperStateTheory.raise_def])
QED

Theorem expr_no_fallthrough_no_success:
  expr_no_fallthrough e ==> eval_expr cx e st <> (INL value,st')
Proof
  Cases_on `e` >> simp[expr_no_fallthrough_def] >>
  rename1 `Call ty target es drv` >> Cases_on `target` >>
  simp[expr_no_fallthrough_def] >>
  simp[raw_revert_no_success, selfdestruct_no_success]
QED

(* Revert data is the original byte vector, with no ABI envelope. *)
Theorem raw_revert_bytes:
  eval_exprs cx es st = (INL [BytesV data], st') ==>
  eval_expr cx (Call ty RawRevert es extra) st =
    (INR (Error (RevertData data)), st')
Proof
  strip_tac >> simp[Once evaluate_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.type_check_def, vyperStateTheory.assert_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
    vyperStateTheory.lift_option_type_def, dest_BytesV_def]
QED

Theorem raw_revert_argument_error:
  eval_exprs cx es st = (INR ex, st') ==>
  eval_expr cx (Call ty RawRevert es extra) st = (INR ex, st')
Proof
  strip_tac >> simp[Once evaluate_def, vyperStateTheory.bind_def]
QED

Theorem raw_revert_cps_bytes:
  vyperSmallStep$apply_vals cx [BytesV data] st (vyperSmallStep$RawRevertK k) =
    vyperSmallStep$AK cx (vyperSmallStep$ApplyExc (Error (RevertData data))) st k
Proof
  simp[Once vyperSmallStepTheory.apply_vals_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.type_check_def, vyperStateTheory.assert_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
    vyperStateTheory.lift_option_type_def, dest_BytesV_def]
QED

(* Account-layer probes for the shared big-step/CPS selfdestruct action.
   The action must use VFM transfer_value, not the checked source transfer.
   Its account transformer is transfer, followed (only for a new contract)
   by zeroing self. Its queue transformer is CONS self, not append. *)
Theorem old_self_beneficiary:
  vfmExecution$transfer_value self self amount accounts = accounts
Proof
  simp[vfmExecutionTheory.transfer_value_def]
QED

Theorem transfer_full_balance:
  self <> beneficiary ==>
  vfmExecution$transfer_value self beneficiary
    (lookup_account self accounts).balance accounts =
  update_account beneficiary
    (lookup_account beneficiary accounts with balance :=
      (lookup_account beneficiary accounts).balance +
      (lookup_account self accounts).balance)
    (update_account self (lookup_account self accounts with balance := 0) accounts)
Proof
  strip_tac >> Cases_on `(lookup_account self accounts).balance = 0` >>
  simp[vfmExecutionTheory.transfer_value_def, vfmStateTheory.update_account_def,
       vfmStateTheory.lookup_account_def, combinTheory.UPDATE_def, FUN_EQ_THM] >>
  gen_tac >> Cases_on `self = x` >> Cases_on `beneficiary = x` >>
  gvs[vfmStateTheory.lookup_account_def, account_state_component_equality]
QED

Theorem new_self_beneficiary:
  update_account self
    (lookup_account self (vfmExecution$transfer_value self self
       (lookup_account self accounts).balance accounts) with balance := 0)
    (vfmExecution$transfer_value self self
       (lookup_account self accounts).balance accounts) =
  update_account self (lookup_account self accounts with balance := 0) accounts
Proof
  simp[old_self_beneficiary]
QED

Theorem zero_self_balance:
  (lookup_account self
    (update_account self (lookup_account self accounts with balance := 0)
      accounts)).balance = 0
Proof
  simp[vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def]
QED

Theorem zero_self_preserves_other:
  other <> self ==>
  lookup_account other
    (update_account self (lookup_account self accounts with balance := 0)
      accounts) = lookup_account other accounts
Proof
  simp[vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       combinTheory.UPDATE_def] >> metis_tac[]
QED

Theorem deletion_prefix_observation:
  TAKE (LENGTH (new ++ old) - LENGTH old) (new ++ old) = new
Proof
  simp[] >> Induct_on `new` >> simp[]
QED

Theorem vfm_deletion_cons:
  (SND (vfmExecution$add_to_delete self s)).rollback.toDelete =
    self :: s.rollback.toDelete
Proof
  EVAL_TAC
QED

Theorem finalize_accounts:
  (finalize_pending_deletions am).accounts =
    vfmExecution$process_deletions am.pending_deletions am.accounts
Proof
  simp[finalize_pending_deletions_def]
QED
