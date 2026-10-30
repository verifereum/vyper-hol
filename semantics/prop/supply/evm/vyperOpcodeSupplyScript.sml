(* TOP-LEVEL: supply_state, supply_action and account-neutral instruction preservation.
 *)
Theory vyperOpcodeSupply
Ancestors
  vyperExecutionSupply vyperPrecompileSupply vyperPrimitiveSupply
  vfmStaticCalls vfmPreserves vfmExecution vfmContext vfmState list
Libs
  proofAuditLib

Definition supply_state_def:
  supply_state budget st <=>
    st.contexts <> [] /\ execution_supply_bound budget st
End

Definition supply_action_def:
  supply_action budget action <=>
    preserves_when (supply_state budget)
      (\st post. supply_state budget post) action
End

Theorem supply_action_cp:
  cp action ==> supply_action budget action
Proof
  rw[supply_action_def, preserves_when_def, supply_state_def]
  >- (drule_all cp_contexts_ne_pair >> simp[]) >>
  drule_all cp_execution_supply >> simp[]
QED

Theorem supply_action_bind:
  supply_action budget action /\ (!x. supply_action budget (next x)) ==>
  supply_action budget (vfmExecution$bind action next)
Proof
  rw[supply_action_def] >> irule preserves_when_bind >> simp[]
QED

Theorem supply_action_ignore_bind:
  supply_action budget action /\ supply_action budget next ==>
  supply_action budget (vfmExecution$ignore_bind action next)
Proof
  simp[vfmExecutionTheory.ignore_bind_def, supply_action_bind]
QED

Theorem supply_action_cond:
  supply_action budget action /\ supply_action budget other ==>
  supply_action budget (if test then action else other)
Proof
  Cases_on `test` >> simp[]
QED

Theorem supply_action_set_current_context:
  supply_action budget (set_current_context ctxt)
Proof
  rw[supply_action_def, preserves_when_def, supply_state_def,
     set_current_context_def, vfmExecutionTheory.return_def, fail_def] >>
  rename1 `before.contexts <> []` >>
  Cases_on `before.contexts` >> gvs[execution_supply_bound_def]
QED

Theorem supply_action_write_storage:
  supply_action budget (write_storage address key value)
Proof
  rw[supply_action_def, preserves_when_def, supply_state_def,
     write_storage_def, vfmExecutionTheory.update_accounts_def,
     vfmExecutionTheory.return_def] >>
  gvs[execution_supply_bound_def] >>
  irule account_supply_bound_install >> simp[]
QED

Theorem supply_action_write_transient_storage:
  supply_action budget (write_transient_storage address key value)
Proof
  rw[supply_action_def, preserves_when_def, supply_state_def,
     write_transient_storage_def, get_tStorage_def, set_tStorage_def,
     vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
     execution_supply_bound_def]
QED

Theorem supply_action_push_logs:
  supply_action budget (push_logs logs)
Proof
  simp[push_logs_def, supply_action_bind, supply_action_cp,
       supply_action_set_current_context]
QED

val supply_tac = rpt (FIRST [
  irule supply_action_cp >> simp[] >> NO_TAC,
  irule supply_action_bind >> conj_tac,
  irule supply_action_ignore_bind >> conj_tac,
  irule supply_action_write_storage,
  irule supply_action_write_transient_storage,
  irule supply_action_push_logs,
  gen_tac >> BETA_TAC]);

Theorem supply_action_step_sstore:
  supply_action budget (step_sstore transient)
Proof
  Cases_on `transient` >> simp[step_sstore_def] >> supply_tac
QED

Theorem supply_action_step_log:
  supply_action budget (step_log topic_count)
Proof
  simp[step_log_def] >> supply_tac
QED

(* CALL/CREATE funding and SELFDESTRUCT burning are the remaining account
   mutations; all other instruction effects preserve this domain. *)
Theorem supply_action_step_inst_no_balance_change:
  op <> SelfDestruct /\ op <> Create /\ op <> Create2 /\
  op <> Call /\ op <> CallCode /\ op <> DelegateCall /\ op <> StaticCall ==>
  supply_action budget (step_inst op)
Proof
  strip_tac >> Cases_on `op = SStore`
  >- gvs[step_inst_def, supply_action_step_sstore] >>
  Cases_on `op = TStore`
  >- gvs[step_inst_def, supply_action_step_sstore] >>
  Cases_on `?topic_count. op = Log topic_count`
  >- gvs[step_inst_def, supply_action_step_log] >>
  irule supply_action_cp >> irule cp_step_inst_non_call >> gvs[]
QED

val () = proofAuditLib.check_theory "vyperOpcodeSupply";
