(* TOP-LEVEL: run_ext_call_supply, run_delegate_call_supply and run_create_evm_supply.
 * Helpers: initial-state and successful-result extraction boundaries.
 *)
Theory vyperAdapterSupply
Ancestors
  vyperRunSupply vyperHandlerSupply vyperBalanceSupply vyperOpcodeSupply
  vyperPrimitiveSupply vyperPrecompileSupply vyperExecutionSupply
  vyperAccountSupply vyperSupplyBoundary vyperInterpreter vyperCreate
  vfmExecution vfmContext vfmState
Libs
  proofAuditLib

val supply_bound_256 = SRULE [] account_supply_bound_256;

Theorem ext_call_initial_supply:
  accounts_supply_bounded accounts /\
  ext_call_value_transfer_ok caller callee value_opt accounts ==>
  supply_state (2 ** 256)
    (make_ext_call_state caller callee code calldata value_opt gas accounts ts txp)
Proof
  rw[supply_state_def] >> FIRST [
    simp[make_ext_call_state_def] >> NO_TAC,
    irule make_ext_call_state_supply >> simp[supply_bound_256]]
QED

Theorem delegate_call_initial_supply:
  accounts_supply_bounded accounts ==>
  supply_state (2 ** 256) (make_delegate_call_state cx target data accounts ts)
Proof
  rw[supply_state_def] >> FIRST [
    (simp[make_delegate_call_state_def] >> pairarg_tac >> simp[]) >> NO_TAC,
    irule make_delegate_call_state_supply >> simp[supply_bound_256]]
QED

Theorem create_initial_supply:
  accounts_supply_bounded accounts /\
  value <= (lookup_account sender accounts).balance ==>
  supply_state (2 ** 256)
    (make_create_state sender address initcode value
      (create_prelude_accounts sender address value accounts) ts pending txp)
Proof
  rw[supply_state_def] >> FIRST [
    simp[make_create_state_def] >> NO_TAC,
    irule make_funded_create_state_supply >> simp[supply_bound_256]]
QED

Theorem extract_call_result_supply:
  accounts_supply_bounded accounts /\ supply_state (2 ** 256) final_state /\
  extract_call_result accounts ts (result,final_state) =
    SOME (success,data,accounts',ts',logs, deletions) ==>
  accounts_supply_bounded accounts'
Proof
  strip_tac >>
  `accounts_supply_bounded final_state.rollback.accounts` by
    gvs[supply_state_def, execution_supply_bound_def, supply_bound_256] >>
  `(result = INR NONE ==> accounts_supply_bounded final_state.rollback.accounts)` by
    simp[] >>
  drule_all extract_call_result_supply_conditional >> simp[]
QED

Theorem extract_create_result_supply:
  accounts_supply_bounded accounts /\ supply_state (2 ** 256) final_state /\
  extract_create_result accounts ts pending (result,final_state) =
    SOME (code,accounts',ts',logs,data,pending') ==>
  accounts_supply_bounded accounts'
Proof
  strip_tac >>
  `accounts_supply_bounded final_state.rollback.accounts` by
    gvs[supply_state_def, execution_supply_bound_def, supply_bound_256] >>
  `(result = INR NONE ==> accounts_supply_bounded final_state.rollback.accounts)` by
    simp[] >>
  drule_all extract_create_result_supply_conditional >> simp[]
QED

Theorem run_call_extract_supply:
  supply_state (2 ** 256) initial /\ accounts_supply_bounded accounts /\
  run_call initial = SOME outcome /\
  extract_call_result accounts ts outcome = SOME (success,data,accounts',ts',logs, deletions) ==>
  accounts_supply_bounded accounts'
Proof
  Cases_on `outcome` >> strip_tac >>
  drule_all run_call_supply >> strip_tac >> gvs[] >>
  drule_all (SRULE [] extract_call_result_supply) >> simp[]
QED

Theorem precompile_extract_supply:
  supply_state (2 ** 256) initial /\ accounts_supply_bounded accounts /\
  extract_call_result accounts ts (dispatch_precompiles address initial) =
    SOME (success,data,accounts',ts',logs, deletions) ==>
  accounts_supply_bounded accounts'
Proof
  strip_tac >>
  `supply_action (2 ** 256)
     (dispatch_precompiles address : execution_state ->
       (unit + vfmExecution$exception option) # execution_state)` by
    (irule supply_action_cp >> simp[]) >>
  drule_all supply_action_snd >> strip_tac >>
  Cases_on `(dispatch_precompiles address initial :
    (unit + vfmExecution$exception option) # execution_state)` >> gvs[] >>
  drule_all (SRULE [] extract_call_result_supply) >> simp[]
QED

Theorem run_call_create_extract_supply:
  supply_state (2 ** 256) initial /\ accounts_supply_bounded accounts /\
  run_call initial = SOME outcome /\
  extract_create_result accounts ts pending outcome =
    SOME (code,accounts',ts',logs,data,pending') ==>
  accounts_supply_bounded accounts'
Proof
  Cases_on `outcome` >> strip_tac >>
  drule_all run_call_supply >> strip_tac >> gvs[] >>
  drule_all (SRULE [] extract_create_result_supply) >> simp[]
QED

Theorem run_ext_call_supply:
  accounts_supply_bounded accounts /\
  run_ext_call caller callee calldata value_opt gas accounts ts txp =
    SOME (success,data,accounts',ts',logs, deletions) ==>
  accounts_supply_bounded accounts'
Proof
  strip_tac >>
  Cases_on `ext_call_value_transfer_ok caller callee value_opt accounts`
  >- (`supply_state (2 ** 256)
         (make_ext_call_state caller callee (lookup_account callee accounts).code
           calldata value_opt gas accounts ts txp)` by
        (irule ext_call_initial_supply >> simp[]) >>
      gvs[run_ext_call_def, AllCaseEqs()] >> FIRST [
        drule_all (SRULE [] run_call_extract_supply) >> simp[],
        drule_all (SRULE [] precompile_extract_supply) >> simp[]]) >>
  gvs[run_ext_call_def, AllCaseEqs()]
QED

Theorem run_delegate_call_supply:
  accounts_supply_bounded accounts /\
  run_delegate_call cx target data accounts ts =
    SOME (success,returndata,accounts',ts',logs, deletions) ==>
  accounts_supply_bounded accounts'
Proof
  strip_tac >>
  `supply_state (2 ** 256) (make_delegate_call_state cx target data accounts ts)` by
    (irule delegate_call_initial_supply >> simp[]) >>
  gvs[run_delegate_call_def, AllCaseEqs()] >> FIRST [
    drule_all (SRULE [] run_call_extract_supply) >> simp[],
    drule_all (SRULE [] precompile_extract_supply) >> simp[]]
QED

(* eval_create establishes affordability before entering this adapter. *)
Theorem run_create_evm_supply:
  accounts_supply_bounded accounts /\
  value <= (lookup_account sender accounts).balance /\
  run_create_evm sender address initcode value accounts ts pending txp =
    SOME (code,accounts',ts',logs,data,pending') ==>
  accounts_supply_bounded accounts'
Proof
  strip_tac >>
  `supply_state (2 ** 256)
     (make_create_state sender address initcode value
       (create_prelude_accounts sender address value accounts) ts pending txp)` by
    (irule create_initial_supply >> simp[]) >>
  `accounts_supply_bounded (create_rollback_accounts sender accounts)` by
    (irule accounts_supply_create_rollback >> simp[]) >>
  gvs[run_create_evm_def, AllCaseEqs()] >>
  drule_all (SRULE [] run_call_create_extract_supply) >> simp[]
QED

val () = proofAuditLib.check_theory "vyperAdapterSupply";
