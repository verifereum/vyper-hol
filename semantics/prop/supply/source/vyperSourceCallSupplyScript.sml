(* TOP-LEVEL: source_supply_action_raw_call, source_supply_action_ext_call,
 * source_supply_action_send.
 * Helpers: direct EVM call-result account bounds and guarded oracle adoption.
 *)
Theory vyperSourceCallSupply
Ancestors
  list pair option vyperSourceSupplyDefs vyperAccountSupply vyperAdapterSupply
  vyperSourcePrimitiveSupply vyperSourceOracleSupply vyperSourceTransferSupply
  vyperInterpreter vyperState vyperCallOutcome extCallOracle
Libs
  vyperSupplyProofLib

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
  run_ext_call caller callee calldata value_opt gas accounts ts txp = SOME payload ==>
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

val call_supply_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [source_supply_reads, source_supply_field_updates,
   source_supply_action_return, source_supply_action_raise,
   source_supply_action_read, source_supply_action_take]);

val call_supply_net = vyperSupplyProofLib.fact_net call_supply_facts
  [source_supply_action_bind, source_supply_action_ignore_bind,
   source_supply_action_accounts_const, source_supply_action_adopt];

(* Only atomic success guards are needed to bound direct-call payloads and
   oracle adoptions; do not unfold their monadic continuations. *)
fun CALL_SUPPLY_BOUND_TAC (goal as (asl,w)) =
  if not (List.exists (fn tm => same_const (fst (strip_comb w)) tm)
      [``accounts_supply_bounded``, ``supply_adoption_safe``])
  then NO_TAC goal
  else
    (POP_ASSUM_LIST (K ALL_TAC) >>
     MAP_EVERY ASSUME_TAC (map ASSUME (List.filter (not o is_forall) asl)) >>
     imp_res_tac source_supply_get_accounts_result >>
     imp_res_tac lift_option_success >>
     imp_res_tac source_supply_take_safe >>
     gvs[] >>
     FIRST [drule_all run_ext_call_supply_payload >> simp[], simp[]] >> NO_TAC) goal;

val CALL_SUPPLY_STEP = FIRST [
  first_assum ACCEPT_TAC, CALL_SUPPLY_BOUND_TAC,
  vyperSupplyProofLib.solve call_supply_net,
  CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac,
  CONV_TAC (RAND_CONV (CHANGED_CONV vyperSupplyProofLib.head_conv)),
  CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
  strip_tac, conj_tac, vyperSupplyProofLib.case_tac];

Theorem source_supply_action_ext_call:
  source_supply_action (eval_ext_call cx static skip_check sig opts values)
Proof
  PairCases_on `sig` >> Cases_on `values` >>
  simp_tac bool_ss [eval_ext_call_def, eval_ext_call_effects_def, LET_THM] >>
  rpt CALL_SUPPLY_STEP
QED

Theorem source_supply_action_send:
  source_supply_action (eval_send cx has_gas values)
Proof
  Cases_on `values` >- simp[eval_send_def, source_supply_action_raise] >>
  rename1 `eval_send _ _ (target::rest)` >>
  Cases_on `rest` >- simp[eval_send_def, source_supply_action_raise] >>
  simp_tac bool_ss [eval_send_def, LET_THM] >> rpt CALL_SUPPLY_STEP
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperSourceCallSupply");
