(* TOP-LEVEL: source_supply_action_raw_call.
 * Helpers: direct EVM call-result account bounds.
 *)
Theory vyperSourceCallSupply
Ancestors
  list pair vyperSourceSupplyDefs vyperAccountSupply vyperAdapterSupply
  vyperInterpreter vyperState

Theorem run_raw_call_supply:
  accounts_supply_bounded accounts /\
  run_raw_call cx flags target calldata amount accounts ts =
    SOME (success,data,accounts',ts',logs, deletions) ==>
  accounts_supply_bounded accounts'
Proof
  Cases_on `flags.rcf_is_delegate` >> gvs[run_raw_call_def] >> strip_tac >> FIRST [
    drule_all run_delegate_call_supply >> simp[],
    drule_all run_ext_call_supply >> simp[]]
QED

Theorem run_ext_call_supply_payload:
  accounts_supply_bounded accounts /\
  run_ext_call caller callee calldata value_opt accounts ts txp = SOME payload ==>
  accounts_supply_bounded (FST (SND (SND payload)))
Proof
  PairCases_on `payload` >> simp[] >> strip_tac >>
  drule_all run_ext_call_supply >> simp[]
QED

Theorem source_supply_action_raw_call:
  source_supply_action (eval_raw_call cx flags target calldata amount)
Proof
  simp[source_supply_action_def] >> qx_gen_tac `before` >> strip_tac >>
  `accounts_supply_bounded before.accounts` by fs[source_supply_def] >>
  Cases_on `~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)` >>
  fs[DE_MORGAN_THM] >>
  simp[eval_raw_call_def, type_check_def, assert_def, bind_def,
       ignore_bind_def, get_accounts_def, get_transient_storage_def,
       return_def, raise_def, DE_MORGAN_THM] >>
  Cases_on `run_raw_call cx flags target calldata amount before.accounts before.tStorage` >>
  simp[lift_option_def, bind_def, return_def, raise_def] >>
  rename1 `run_raw_call _ _ _ _ _ _ _ = SOME call_result` >>
  PairCases_on `call_result` >>
  rename1 `run_raw_call _ _ _ _ _ _ _ =
    SOME (success,data,accounts_out,tstorage_out,event_list,deletions)` >>
  drule_all run_raw_call_supply >> strip_tac >>
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `success` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  gvs[update_accounts_def, update_transient_def, append_logs_def, update_pending_deletions_def,
      bind_def, ignore_bind_def, return_def, raise_def, source_supply_def,
      evaluation_state_accfupds]
QED

Theorem source_supply_action_send:
  source_supply_action (eval_send cx target amount)
Proof
  simp[eval_send_def] >> irule source_supply_action_bind_simple >>
  simp[source_supply_action_raw_call] >> qx_gen_tac `answer` >>
  Cases_on `answer = Value (BoolV T)` >>
  simp[source_supply_action_def, check_def, assert_def, ignore_bind_def,
       bind_def, return_def, raise_def]
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperSourceCallSupply");
