(* TOP-LEVEL: supply_action_step.
 * Helpers: code deposit, exception handling and child-frame incorporation.
 *)
Theory vyperHandlerSupply
Ancestors
  vyperExecutionSupply vyperPrecompileSupply vyperPrimitiveSupply
  vyperOpcodeSupply vyperBalanceSupply vyperCallSupply
  vfmExecutionProp vfmStaticCalls vfmDecreasesGas vfmPreserves
  vfmExecution vfmContext vfmState list arithmetic
Libs
  BasicProvers

Theorem supply_action_step_inst:
  supply_action budget (step_inst op)
Proof
  Cases_on `op = SelfDestruct`
  >- gvs[step_inst_def, supply_action_step_self_destruct] >>
  Cases_on `op = Create`
  >- gvs[step_inst_def, supply_action_step_create] >>
  Cases_on `op = Create2`
  >- gvs[step_inst_def, supply_action_step_create] >>
  Cases_on `op = Call`
  >- gvs[step_inst_def, supply_action_step_call] >>
  Cases_on `op = CallCode`
  >- gvs[step_inst_def, supply_action_step_call] >>
  Cases_on `op = DelegateCall`
  >- gvs[step_inst_def, supply_action_step_call] >>
  Cases_on `op = StaticCall`
  >- gvs[step_inst_def, supply_action_step_call] >>
  irule supply_action_step_inst_no_balance_change >> simp[]
QED

Theorem supply_action_snd:
  supply_action budget action /\ supply_state budget st ==>
  supply_state budget (SND (action st))
Proof
  strip_tac >> Cases_on `action st` >>
  rename1 `action st = (result,post)` >> simp[] >>
  irule supply_action_result >> qexistsl_tac [`action`, `result`, `st`] >> simp[]
QED

Theorem supply_bind_snd:
  supply_state budget (SND (first st)) /\
  (!value. supply_action budget (next value)) ==>
  supply_state budget (SND (vfmExecution$bind first next st))
Proof
  strip_tac >> Cases_on `first st` >>
  rename1 `first st = (outcome,mid)` >> Cases_on `outcome` >>
  gvs[vfmExecutionTheory.bind_def] >>
  irule supply_action_snd >> simp[]
QED

Theorem supply_action_install_code:
  supply_action budget (vfmExecution$update_accounts (\accounts.
    update_account address (lookup_account address accounts with code := code) accounts))
Proof
  rw[supply_action_def, preserves_when_def, supply_state_def,
     vfmExecutionTheory.update_accounts_def, vfmExecutionTheory.return_def] >>
  gvs[execution_supply_bound_def] >>
  irule account_supply_bound_install >> simp[]
QED

val handler_supply_step = FIRST [
  irule supply_action_cp >> simp[] >> NO_TAC,
  irule supply_action_step_inst,
  irule supply_action_bind >> conj_tac,
  irule supply_action_ignore_bind >> conj_tac,
  irule supply_action_install_code,
  gen_tac >> BETA_TAC,
  TOP_CASE_TAC];

Theorem supply_action_handle_create:
  supply_action budget (handle_create error)
Proof
  Cases_on `error` >> simp[handle_create_def] >> rpt handler_supply_step
QED

Theorem pop_and_incorporate_supply:
  supply_state budget st /\ 1 < LENGTH st.contexts ==>
  supply_state budget (SND (pop_and_incorporate_context success st))
Proof
  strip_tac >> Cases_on `st.contexts` >> gvs[] >>
  rename1 `st.contexts = callee::parents` >>
  Cases_on `parents` >> gvs[] >>
  gvs[pop_and_incorporate_context_def, get_gas_left_def,
      get_current_context_def, pop_context_def, unuse_gas_def,
      vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
      vfmExecutionTheory.ignore_bind_def, assert_def, fail_def,
      push_logs_def, update_gas_refund_def, set_current_context_def,
      set_rollback_def, supply_state_def, execution_supply_bound_def,
      AllCaseEqs()] >>
  IF_CASES_TAC >> Cases_on `success` >>
  gvs[vfmExecutionTheory.return_def, vfmExecutionTheory.bind_def,
      vfmExecutionTheory.ignore_bind_def, get_current_context_def,
      set_current_context_def, set_rollback_def,
      supply_state_def, execution_supply_bound_def]
QED

Theorem handle_ex_helper_supply_state:
  supply_state budget st ==>
  supply_state budget (SND (handle_ex_helper error st))
Proof
  strip_tac >> `st.contexts <> []` by gvs[supply_state_def] >>
  simp[handle_ex_helper_def, get_num_contexts_def,
       vfmExecutionTheory.bind_def, vfmExecutionTheory.return_def] >>
  Cases_on `LENGTH st.contexts <= 1`
  >- gvs[reraise_def] >>
  simp[get_return_data_def, get_output_to_def, get_current_context_def,
       vfmExecutionTheory.bind_def, vfmExecutionTheory.ignore_bind_def,
       vfmExecutionTheory.return_def] >>
  `supply_state budget
     (SND (pop_and_incorporate_context (error = NONE) st))` by
    (irule pop_and_incorporate_supply >> simp[]) >>
  Cases_on `pop_and_incorporate_context (error = NONE) st` >>
  rename1 `pop_and_incorporate_context (error = NONE) st = (outcome,mid)` >>
  Cases_on `outcome` >> gvs[] >>
  irule supply_action_snd >> simp[supply_action_cp]
QED

Theorem supply_action_handle_ex_helper:
  supply_action budget (handle_ex_helper error)
Proof
  rw[supply_action_def, preserves_when_def] >>
  drule_then (qspec_then `error` mp_tac) handle_ex_helper_supply_state >> gvs[]
QED

Theorem supply_action_handle_exception:
  supply_action budget (handle_exception error)
Proof
  rw[supply_action_def, preserves_when_def, handle_exception_decomp] >>
  qmatch_asmsub_abbrev_tac `action before = (outcome,after)` >>
  `supply_action budget action` by
    (simp[Abbr `action`] >> rpt (FIRST [
       irule supply_action_cp >> simp[] >> NO_TAC,
       irule supply_action_handle_ex_helper,
       irule supply_action_bind >> conj_tac,
       irule supply_action_ignore_bind >> conj_tac,
       gen_tac >> BETA_TAC])) >>
  drule_all supply_action_result >> simp[]
QED

Theorem supply_action_handle:
  supply_action budget first /\ (!error. supply_action budget (next error)) ==>
  supply_action budget (vfmExecution$handle first next)
Proof
  rw[supply_action_def] >> irule preserves_when_handle >> simp[]
QED

Theorem supply_action_handle_step:
  supply_action budget (handle_step error)
Proof
  Cases_on `vfm_abort error` >> simp[handle_step_def] >> FIRST [
    irule supply_action_cp >> simp[] >> NO_TAC,
    irule supply_action_handle >>
      simp[supply_action_handle_create, supply_action_handle_exception]]
QED

Theorem supply_action_step_inner:
  supply_action budget step_inner
Proof
  simp[step_inner_def] >> rpt handler_supply_step
QED

Theorem supply_action_step:
  supply_action budget vfmExecution$step
Proof
  simp[step_eq_handle_step_inner] >> irule supply_action_handle >>
  simp[supply_action_step_inner, supply_action_handle_step]
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperHandlerSupply");
