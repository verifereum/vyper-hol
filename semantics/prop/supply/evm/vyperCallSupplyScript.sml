(* TOP-LEVEL: supply_action_step_call and supply_action_step_create.
 * Helpers: snapshot-aware composition and funded child preparation.
 *)
Theory vyperCallSupply
Ancestors
  vyperExecutionSupply vyperPrecompileSupply vyperPrimitiveSupply
  vyperOpcodeSupply vyperBalanceSupply vfmExecutionProp vfmStaticCalls
  vfmPreserves vfmExecution vfmContext vfmState list
Libs
  proofAuditLib

(* A local precondition for the account snapshot read by CALL/CREATE. *)
Definition snapshot_supply_def:
  snapshot_supply budget accounts action <=>
    preserves_when
      (\st. supply_state budget st /\ st.rollback.accounts = accounts)
      (\st post. supply_state budget post) action
End

Theorem snapshot_supply_result:
  snapshot_supply budget accounts action /\ action st = (result,post) /\
  supply_state budget st /\ st.rollback.accounts = accounts ==>
  supply_state budget post
Proof
  rw[snapshot_supply_def, preserves_when_def] >> first_x_assum irule >>
  qexistsl_tac [`result`, `st`] >> simp[]
QED

Theorem snapshot_supply_action:
  supply_action budget action ==> snapshot_supply budget accounts action
Proof
  strip_tac >> simp[snapshot_supply_def, preserves_when_def] >>
  rpt gen_tac >> strip_tac >> drule_all supply_action_result >> simp[]
QED

Theorem snapshot_supply_cp:
  cp action ==> snapshot_supply budget accounts action
Proof
  strip_tac >> irule snapshot_supply_action >>
  irule supply_action_cp >> simp[]
QED

Theorem snapshot_supply_bind:
  cp first /\ (!value. snapshot_supply budget accounts (next value)) ==>
  snapshot_supply budget accounts (vfmExecution$bind first next)
Proof
  strip_tac >>
  simp[snapshot_supply_def, preserves_when_def, vfmExecutionTheory.bind_def] >>
  qx_genl_tac [`before`, `outcome`, `after`] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all cp_result_supply >> strip_tac >> gvs[] >>
  rename1 `first before = (INL value,mid)` >>
  qpat_x_assum `!value. snapshot_supply _ _ _`
    (qspec_then `value` assume_tac) >>
  drule_all snapshot_supply_result >> simp[]
QED

Theorem snapshot_supply_ignore_bind:
  cp first /\ snapshot_supply budget accounts next ==>
  snapshot_supply budget accounts (vfmExecution$ignore_bind first next)
Proof
  rw[vfmExecutionTheory.ignore_bind_def] >>
  irule snapshot_supply_bind >> simp[]
QED

Theorem supply_action_get_accounts:
  (!accounts. snapshot_supply budget accounts (next accounts)) ==>
  supply_action budget (vfmExecution$bind get_accounts next)
Proof
  strip_tac >>
  simp[supply_action_def, preserves_when_def, get_accounts_def,
       vfmExecutionTheory.bind_def, vfmExecutionTheory.return_def] >>
  qx_genl_tac [`before`, `outcome`, `after`] >> strip_tac >>
  qpat_x_assum `!accounts. snapshot_supply _ _ _`
    (qspec_then `before.rollback.accounts` assume_tac) >>
  irule snapshot_supply_result >>
  qexistsl_tac [`before.rollback.accounts`, `next before.rollback.accounts`,
               `outcome`, `before`] >> simp[]
QED

Theorem proceed_call_supply_state:
  supply_state budget st /\
  value <= (lookup_account sender st.rollback.accounts).balance ==>
  supply_state budget
    (SND (proceed_call op sender address value argsOffset argsSize code stipend outputTo st))
Proof
  rw[supply_state_def] >>
  drule_all proceed_call_supply >> simp[]
QED

Theorem proceed_create_supply_state:
  supply_state budget st /\
  value <= (lookup_account sender st.rollback.accounts).balance ==>
  supply_state budget
    (SND (proceed_create sender address value code cappedGas st))
Proof
  rw[supply_state_def] >>
  drule_all proceed_create_supply >> simp[]
QED

Theorem snapshot_supply_proceed_call:
  value <= (lookup_account sender accounts).balance ==>
  snapshot_supply budget accounts
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
Proof
  rw[snapshot_supply_def, preserves_when_def] >> gvs[] >>
  drule_all_then
    (qspecl_then [`stipend`, `outputTo`, `op`, `code`, `argsSize`,
                  `argsOffset`, `address`] mp_tac) proceed_call_supply_state >>
  gvs[]
QED

Theorem snapshot_supply_proceed_create:
  value <= (lookup_account sender accounts).balance ==>
  snapshot_supply budget accounts
    (proceed_create sender address value code cappedGas)
Proof
  rw[snapshot_supply_def, preserves_when_def] >> gvs[] >>
  drule_all_then (qspecl_then [`code`, `cappedGas`, `address`] mp_tac)
    proceed_create_supply_state >> gvs[]
QED

Theorem supply_action_increment_nonce:
  supply_action budget (vfmExecution$update_accounts (increment_nonce address))
Proof
  rw[supply_action_def, preserves_when_def, supply_state_def,
     vfmExecutionTheory.update_accounts_def, vfmExecutionTheory.return_def] >>
  gvs[execution_supply_bound_def] >>
  irule account_supply_bound_nonce >> simp[]
QED

Theorem supply_action_abort_create_exists:
  supply_action budget (abort_create_exists sender)
Proof
  simp[abort_create_exists_def] >>
  irule supply_action_ignore_bind >> conj_tac
  >- irule supply_action_increment_nonce >>
  irule supply_action_cp >> simp[]
QED

val call_supply_step = FIRST [
  CHANGED_TAC (simp[pairTheory.UNCURRY]),
  irule supply_action_cp >> simp[] >> NO_TAC,
  irule supply_action_get_accounts,
  irule supply_action_bind >> conj_tac,
  irule supply_action_ignore_bind >> conj_tac,
  irule snapshot_supply_cp >> simp[] >> NO_TAC,
  irule snapshot_supply_bind >> conj_tac,
  irule snapshot_supply_ignore_bind >> conj_tac,
  irule snapshot_supply_proceed_call >> gvs[] >> NO_TAC,
  irule snapshot_supply_proceed_create >> gvs[] >> NO_TAC,
  irule snapshot_supply_action >> irule supply_action_abort_create_exists,
  gen_tac >> BETA_TAC,
  COND_CASES_TAC];

Theorem supply_action_step_call:
  supply_action budget (step_call op)
Proof
  simp[step_call_def] >>
  NTAC 20 (TRY call_supply_step) >> rpt call_supply_step
QED

Theorem supply_action_step_create:
  supply_action budget (step_create two)
Proof
  simp[step_create_def] >>
  NTAC 20 (TRY call_supply_step) >> rpt call_supply_step
QED

val () = proofAuditLib.check_theory "vyperCallSupply";
