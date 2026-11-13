(* PLAN 5.5 boundary, not a compiler correctness certificate.
 * TOP-LEVEL: layouts_agree, source_deployment_rel, source_typing_ok,
 * source_storage_ok, call_outcomes_storage_ok, tx_block_fields_rel,
 * tx_env_ok (defined in compileEnv, as part of call_ctx_rel),
 * value_transfer_ok, accounts_after_transfer, call_state_rel,
 * call_external_transaction_pending_deletions,
 * load_contract_pending_deletions, valid_vyper_call, compiled_event_info,
 * return_bytes, tx_return_bytes,
 * unspecified_behaviour_exempt, source_exempt, gas_readings_rel,
 * call_success_rel, exception_outcome_rel, call_result_rel, logs_correspond.
 * Transaction boundary (Milestone 7 lifecycle): next_source_machine.
 * TASK056: all compiler/call consumers use this exact boundary; the obsolete
 * compatibility owner is deleted. No old/new equivalence is claimed.
 * DAG: source/typing/storage + supported syntax + frame/trace -> e2eDefs;
 * e2eDefs -> entry/producers/composition -> e2eCorrectness.
 *)
Theory e2eDefs
Ancestors
  vfmExecution vfmExecutionProp vfmState vfmRunCall
  vfmTotalBalance vfmReturndataBound vfmWfState
  frameOutcome callTrace
  vyperABI vyperEvent vyperInterpreter vyperCall
  vyperTypeContract vyperTypeContractSoundness vyperTypeInitialState
  vyperStorageLayoutSafety vyperStorageFootprint vyperRuntimeAccounts
  supportedProgram compileEnv loweringStateRelDefs selectorDispatch immutableSectionRel context
  sorting

(* ===== Source deployment, typing and storage ===== *)

Definition layouts_agree_def:
  layouts_agree tops am tx <=>
    let (sl, tl) = (case ALOOKUP am.layouts tx.target of
                      SOME p => p | NONE => ([], [])) in
      (!vis id ty slot_opt. MEM (VariableDecl vis Storage id ty slot_opt) tops ==>
                            ALOOKUP sl (NONE, id) = slot_opt) /\
      (!vis id ty slot_opt. MEM (VariableDecl vis Transient id ty slot_opt) tops ==>
                            ALOOKUP tl (NONE, id) = slot_opt) /\
      (!vis tr id kt vt slot_opt. MEM (HashMapDecl vis tr id kt vt slot_opt) tops ==>
                                  ALOOKUP (if tr then tl else sl) (NONE, id) = slot_opt) /\
      (* The pinned frontend reserves this slot when a guard is present.
         Ordinary contracts need not have a transient layout at all. *)
      (!vis mut rr name args dflts ret body.
         MEM (FunctionDecl vis mut T rr name args dflts ret body) tops ==>
         ALOOKUP tl (NONE, "$.nonreentrant_key") =
           SOME global_nonreentrant_slot)
End

Theorem layouts_agree_nonreentrant_slot:
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops ==>
  lookup_nonreentrant_slot am.layouts tx.target = SOME global_nonreentrant_slot
Proof
  strip_tac >> Cases_on `ALOOKUP am.layouts tx.target`
  >- (fs[layouts_agree_def] >> metis_tac[]) >>
  rename1 `ALOOKUP am.layouts tx.target = SOME lay` >>
  PairCases_on `lay` >>
  fs[layouts_agree_def, lookup_nonreentrant_slot_def] >> metis_tac[]
QED

Theorem layouts_agree_initial_nonreentrant_slot:
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops ==>
  (initial_evaluation_context am.sources am.layouts tx NONE).nonreentrant_slot =
    SOME global_nonreentrant_slot
Proof
  simp[initial_evaluation_context_def] >>
  metis_tac[layouts_agree_nonreentrant_slot]
QED

(* The target has no exports, or an empty export entry: load_contract
   installs SOME [] for a contract without exported module functions, and
   both make call_external use the main module. *)
Definition source_deployment_rel_def:
  source_deployment_rel tops am tx <=>
    ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
    (ALOOKUP am.exports tx.target = NONE \/
     ALOOKUP am.exports tx.target = SOME []) /\
    layouts_agree tops am tx
End

Theorem source_deployment_context:
  source_deployment_rel tops am tx ==>
  get_tenv (initial_evaluation_context am.sources am.layouts tx NONE) =
    type_env tops /\
  get_module_code (initial_evaluation_context am.sources am.layouts tx NONE)
    NONE = SOME tops
Proof
  simp[source_deployment_rel_def, initial_evaluation_context_def,
       vyperContextTheory.get_tenv_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.type_env_all_modules_def,
       vyperContextTheory.type_env_def, finite_mapTheory.FUNION_FEMPTY_2] >>
  rpt strip_tac >> simp[]
QED

Definition source_typing_ok_def:
  source_typing_ok tops am tx <=>
    ?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
          checked_contract_runtime_ready art [(NONE, tops)] am tx /\
          machine_well_typed am /\ call_tx_well_typed tx
End

Definition source_storage_ok_def:
  source_storage_ok am tx os gs <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
    let obs = source_storage_trace am tx os gs in
    let (regions, locks) = storage_trace_horizon obs in
      storage_roots_fit obs ∧ regions_consistent regions ∧
      storage_locks_separated regions locks ∧
      storage_well_formed_on cx (initial_state am []) regions
End

Definition call_outcomes_storage_ok_def:
  call_outcomes_storage_ok am tx os gs <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
    let obs = source_storage_trace am tx os gs in
      storage_trace_backends_well_formed cx
        (FST (storage_trace_horizon obs)) obs
End

(* The global storage-and-bounds predicate remains available independently.
   The compiler boundary uses the finite selected-trace guards above. *)
Definition call_outcomes_ok_def:
  call_outcomes_ok am tx os <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
      EVERY (\outcome.
               LENGTH outcome.co_returnData < dimword(:256) /\
               accounts_runtime_well_typed outcome.co_accounts /\
               contract_storage_well_formed cx
                 (initial_state (am with <| accounts := outcome.co_accounts;
                                            tStorage := outcome.co_tStorage |>) []))
            os
End

(* ===== Transaction environment and entry transfer ===== *)

(* tx_env_ok is compileEnv's, part of call_ctx_rel. *)

Definition tx_block_fields_rel_def:
  tx_block_fields_rel tx txp <=>
    txp.origin = tx.origin /\ txp.gasPrice = tx.gas_price /\
    txp.baseFeePerGas = tx.base_fee /\ txp.blockNumber = tx.block_number /\
    txp.blockTimeStamp = tx.time_stamp /\ txp.blockCoinBase = tx.coinbase /\
    txp.blockGasLimit = tx.gas_limit /\ txp.chainId = tx.chain_id /\
    txp.blobHashes = tx.blob_hashes /\
    txp.baseFeePerBlobGas = tx.blob_base_fee /\
    txp.prevRandao = n2w tx.prev_randao /\
    txp.prevHashes = tx.block_hashes /\ tx_env_ok tx
End

Definition value_transfer_ok_def:
  value_transfer_ok tx accounts <=>
    tx.value = 0 \/ tx.sender = tx.target \/
    (tx.value <= (lookup_account tx.sender accounts).balance /\
     (lookup_account tx.target accounts).balance + tx.value < 2 ** 256)
End

Definition accounts_after_transfer_def:
  accounts_after_transfer tx accounts =
    if tx.value = 0 \/ tx.sender = tx.target then accounts
    else
      let sender = lookup_account tx.sender accounts in
      let recipient = lookup_account tx.target accounts in
        (update_account tx.sender (sender with balance updated_by (flip $- tx.value)) o
         update_account tx.target (recipient with balance updated_by ($+ tx.value)))
        accounts
End

(* ===== Fresh nonstatic frame: LIVE post-transfer accounts ===== *)

Definition account_immutables_def:
  account_immutables (am:abstract_machine) addr =
    case ALOOKUP am.immutables addr of
      NONE => empty_immutables
    | SOME imms => imms
End

Definition call_state_rel_def:
  call_state_rel tops runtime_bc am tx es <=>
    ?ctxt rb rest.
      es.contexts = (ctxt, rb) :: rest /\
      wf_state es /\ (?d. es.msdomain = Collect d) /\
      ctxt.jumpDest = NONE /\ ~ctxt.msgParams.static /\ ~tx.is_static /\
      (?mr. ctxt.msgParams.outputTo = Memory mr) /\
      installed_code_rel tops runtime_bc (account_immutables am tx.target)
        ctxt.msgParams.code /\
      (lookup_account tx.target es.rollback.accounts).code =
        ctxt.msgParams.code /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY ctxt.msgParams.code /\
      LENGTH ctxt.msgParams.code <= 24576 /\
      ctxt.pc = 0 /\ ctxt.stack = [] /\ ctxt.logs = [] /\
      ctxt.returnData = [] /\ buffer_to_list ctxt.memory = [] /\
      balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es /\
      value_transfer_ok tx am.accounts /\
      es.rollback.accounts = accounts_after_transfer tx am.accounts /\
      es.rollback.toDelete = am.pending_deletions /\
      es.rollback.tStorage = am.tStorage /\ am.logs = [] /\
      am.pending_deletions = [] /\
      ctxt.msgParams.caller = tx.sender /\ ctxt.msgParams.callee = tx.target /\
      ctxt.msgParams.value = tx.value /\
      buffer_to_list ctxt.msgParams.data = tx.calldata /\
      ctxt.msgParams.code = tx.code /\
      tx_block_fields_rel tx es.txParams /\
      source_deployment_rel tops am tx
End

(* ===== Outcome bounds of the real run ===== *)

(* Every outcome call_trace records is outcome_of a state the run reaches:
   the return data of its top frame and its live accounts.  wf_state bounds
   every account's code (wf_accounts), balance_bounded every account map's
   total balance, returndata_bounded every frame's return data, and a step
   keeps all three. *)
Theorem outcome_of_bounded[local]:
  wf_state s /\ balance_bounded (2 ** 256 - 1) s /\ returndata_bounded s ==>
  LENGTH (outcome_of k s n m).co_returnData < dimword(:256) /\
  accounts_runtime_well_typed (outcome_of k s n m).co_accounts
Proof
  strip_tac >>
  simp[outcome_of_def, accounts_runtime_well_typed_def,
       account_runtime_well_typed_def] >> conj_tac
  >- (CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
      Cases_on `s.contexts` >> gvs[wf_state_def, returndata_bounded_def])
  >> gen_tac >> conj_tac
  >- (drule balance_bounded_rollback >> strip_tac >>
      irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
      qexists_tac `total_balance s.rollback.accounts` >>
      simp[lookup_balance_le_total_balance] >>
      pop_assum mp_tac >> simp[])
  >> `wf_accounts s.rollback.accounts` by fs[wf_state_def, all_accounts_def] >>
  fs[wf_accounts_def, wf_account_state_def, lookup_account_def] >>
  first_x_assum (qspec_then `addr` mp_tac) >> simp[]
QED

Theorem step_outcome_invariant[local]:
  wf_state s /\ balance_bounded (2 ** 256 - 1) s /\ returndata_bounded s /\
  step s = (r, s') ==>
  wf_state s' /\ balance_bounded (2 ** 256 - 1) s' /\ returndata_bounded s'
Proof
  strip_tac >>
  drule step_preserves_wf_state >> drule step_returndata_bounded >>
  fs[balance_bounded_def] >> drule_all step_total_balance_bounded >>
  fs[]
QED

Theorem frame_obs_tr_every_outcome:
  !d obs s r s'.
    (!t. Inv t ==> Inv (SND (step t))) /\
    (!t k n m. Inv t ==> Q (outcome_of k t n m)) /\
    Inv s' /\ EVERY Q (MAP SND obs.entries) ==>
    EVERY Q (MAP SND (frame_obs_tr d obs s (r,s')).entries)
Proof
  recInduct frame_obs_tr_ind >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `EVERY Q (MAP SND (observe d s (r,s') obs).entries)` by
    (simp[observe_def] >> rw[] >> BasicProvers.every_case_tac >>
     gvs[listTheory.EVERY_APPEND]) >>
  `Inv (SND (step s'))` by (first_assum irule >> fs[]) >>
  simp[Once frame_obs_tr_def] >>
  IF_CASES_TAC >- fs[] >>
  first_x_assum (qspec_then `observe d s (r,s') obs` mp_tac) >>
  fs[] >> Cases_on `step s'` >> fs[]
QED

Theorem call_trace_outcomes_bounded:
  wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es ==>
  EVERY (\co. LENGTH co.co_returnData < dimword(:256) /\
              accounts_runtime_well_typed co.co_accounts)
    (MAP SND (call_trace es))
Proof
  strip_tac >> REWRITE_TAC[call_trace_def, frame_obs_def] >>
  Cases_on `step es` >>
  drule_all step_outcome_invariant >> strip_tac >>
  irule frame_obs_tr_every_outcome >>
  reverse conj_tac >- simp[] >>
  qexists_tac `\t. wf_state t /\ balance_bounded (2 ** 256 - 1) t /\
                   returndata_bounded t` >>
  BETA_TAC >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >> drule_all outcome_of_bounded >> simp[]) >>
  rpt strip_tac >> Cases_on `step t` >>
  drule_all step_outcome_invariant >> simp[]
QED

Theorem call_state_rel_call_outcomes_ok:
  call_state_rel tops runtime_bc am tx es /\
  EVERY (\outcome.
    contract_storage_well_formed
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state (am with <| accounts := outcome.co_accounts;
                                tStorage := outcome.co_tStorage |>) []))
    (MAP SND (call_trace es)) ==>
  call_outcomes_ok am tx (MAP SND (call_trace es))
Proof
  strip_tac >>
  `wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es` by
    fs[call_state_rel_def] >>
  drule_all call_trace_outcomes_bounded >>
  qpat_x_assum `EVERY _ (MAP SND (call_trace es))` mp_tac >>
  simp[call_outcomes_ok_def, listTheory.EVERY_MEM] >>
  rpt strip_tac >> res_tac
QED

(* The source machine the next transaction starts from, after a transaction
   or deployment whose frame succeeded (r = INR NONE) in EVM state es' with
   source machine am': it adopts the EVM's committed accounts (pending
   deletions processed, the target's installed code included), and starts the
   transaction with empty transient storage, no logs and no pending deletions.
   After a failed top-level frame es'.rollback still holds the frame's writes
   (the transaction's accounting discards them), so the next transaction
   starts from the pre-transaction machine instead. *)
Definition next_source_machine_def:
  next_source_machine (am' : abstract_machine) es' =
    am' with <| accounts := process_deletions es'.rollback.toDelete
                              es'.rollback.accounts;
                tStorage := empty_transient_storage;
                logs := [];
                pending_deletions := [] |>
End

(* call_state_rel's am.pending_deletions = [] holds of every machine that
   deployments and transactions reach from one with none: a successful
   deployment or call commits its deletions (finalize_pending_deletions),
   and a failed call returns the machine it was given. *)
Theorem call_external_transaction_pending_deletions:
  !orc gobs am tx r am' rqs.
    call_external_transaction orc gobs am tx = (r, am', rqs) /\
    am.pending_deletions = [] ==>
    am'.pending_deletions = []
Proof
  rw[call_external_transaction_def] >> Cases_on `r`
  >- (fs[call_external_def, call_external_trace_def, AllCaseEqs()] >> gvs[]) >>
  rename1 `call_external orc gobs (clear_machine_logs am) tx = (INR exn, am', rqs)` >>
  reverse (Cases_on `exn = HaltException`)
  >- (drule call_external_error_rollback >> simp[clear_machine_logs_def]) >>
  gvs[call_external_def, call_external_trace_def, AllCaseEqs()]
QED

Theorem load_contract_pending_deletions:
  !orc gobs am tx mods exps am' rqs.
    load_contract orc gobs am tx mods exps = INL (am', rqs) ==>
    am'.pending_deletions = []
Proof
  rw[load_contract_def, load_contract_trace_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Exact PLAN lookup: the source lookup_function API, no invented additional
   MEM/selector-uniqueness premise. Supported-program restrictions are separate. *)
Definition valid_vyper_call_def:
  valid_vyper_call tops tx calldata ret <=>
    ?mut args body.
      vyperInterpreter$lookup_function NONE tx.function_name External tops =
        SOME (mut, F, args, [], ret, body) /\
      tx.function_name <> "__default__" /\
      LENGTH tx.args = LENGTH args /\
      IS_SOME (bind_arguments (type_env tops) args tx.args) /\
      calldata_encodes (type_env tops) tx.function_name (MAP SND args)
        tx.args calldata
End

Definition compiled_event_info_def:
  compiled_event_info program =
    build_event_info (type_env program) program
      ((K NONE) : string -> (num # type list # bool list) option)
End

(* ===== Canonical external return encoding and the ONLY exemption ===== *)

Definition return_bytes_def:
  return_bytes tops ret v out <=>
    if ret = NoneT then out = []
    else ?abi_v.
           vyper_to_abi (type_env tops) ret v = SOME abi_v /\
           out = if needs_external_call_wrap ret
                 then enc (Tuple [vyper_to_abi_type (type_env tops) ret])
                          (ListV [abi_v])
                 else enc (vyper_to_abi_type (type_env tops) ret) abi_v
End

(* Observe the selected function's decorator at the transaction boundary. *)
Definition tx_return_bytes_def:
  tx_return_bytes tops ret tx v out <=>
    if lookup_raw_return_or_F (NONE : num option) tx.function_name External tops
    then raw_return_bytes v = SOME out
    else return_bytes tops ret v out
End

Definition unspecified_behaviour_exempt_def:
  unspecified_behaviour_exempt tops e <=>
    e = RuntimeError "abi_decode invalid" /\
    ?ty. occurs_abi_decode_target ty tops /\
         is_dynamic (vyper_to_abi_type (type_env tops) ty)
End

Definition source_exempt_def:
  source_exempt tops (src : (value + exception) # abstract_machine # call_request list) <=>
    case FST src of INR (Error e) => unspecified_behaviour_exempt tops e | _ => F
End

(* ===== Log Correspondence ===== *)

(* Source execution now records the concrete EVM event directly. The metadata
   parameters remain temporarily for compatibility with the e2e API. *)
Definition log_entry_corresponds_def:
  log_entry_corresponds _ _ _ (source_event : log) (ev : event) <=>
    source_event = ev
End

(* Compatibility lemmas between the executable semantics encoder and the
   pre-existing relational log specification in compileEnv. *)
Theorem event_value_to_word_eq_val_to_w256:
  event_value_to_word v = val_to_w256 v
Proof
  Cases_on `v` >>
  simp[event_value_to_word_def, valueEncodingTheory.val_to_w256_def]
QED

Theorem encode_event_topic_eq_log_topic_equiv:
  encode_event_topic ty v = SOME topic <=>
  log_topic_equiv ty v topic
Proof
  Cases_on `is_event_bytestring_type ty` >> Cases_on `v` >>
  simp[encode_event_topic_def, log_topic_equiv_def,
       log_bytestring_topic_def, byteTheory.word_of_bytes_be_def] >>
  metis_tac[]
QED

Theorem encode_indexed_event_topics_characterization:
  encode_indexed_event_topics flags tys vals = SOME topics <=>
  LENGTH flags = LENGTH tys /\
  LENGTH flags = LENGTH vals /\
  log_indexed_topics_equiv
    (indexed_topic_flags flags tys)
    (indexed_values flags vals) topics
Proof
  qid_spec_tac `topics` >> qid_spec_tac `vals` >> qid_spec_tac `tys` >>
  Induct_on `flags`
  >- (Cases_on `tys` >> Cases_on `vals` >> Cases_on `topics` >>
      simp[encode_indexed_event_topics_def, indexed_topic_flags_def,
           indexed_values_def, log_indexed_topics_equiv_def])
  >> qx_gen_tac `flag` >> qx_gen_tac `tys` >>
  qx_gen_tac `vals` >> qx_gen_tac `topics` >>
  Cases_on `tys` >> Cases_on `vals` >> Cases_on `flag` >>
  Cases_on `topics` >>
  gvs[encode_indexed_event_topics_def, indexed_topic_flags_def,
      indexed_values_def, log_indexed_topics_equiv_def,
      is_event_bytestring_type_def, is_bytestring_type_def,
      encode_event_topic_eq_log_topic_equiv, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem non_indexed_event_args_characterization:
  non_indexed_event_args flags tys vals = SOME typed_vals <=>
  LENGTH flags = LENGTH tys /\
  LENGTH flags = LENGTH vals /\
  MAP FST typed_vals = log_non_indexed_types flags tys /\
  MAP SND typed_vals = log_non_indexed_values flags vals
Proof
  qid_spec_tac `typed_vals` >> qid_spec_tac `vals` >>
  qid_spec_tac `tys` >> Induct_on `flags`
  >- (Cases_on `tys` >> Cases_on `vals` >> Cases_on `typed_vals` >>
      simp[non_indexed_event_args_def, log_non_indexed_types_def,
           log_non_indexed_values_def])
  >> qx_gen_tac `flag` >> qx_gen_tac `tys` >>
  qx_gen_tac `vals` >> qx_gen_tac `typed_vals` >>
  Cases_on `tys` >> Cases_on `vals` >> Cases_on `flag` >>
  Cases_on `typed_vals` >>
  gvs[non_indexed_event_args_def, log_non_indexed_types_def,
      log_non_indexed_values_def, AllCaseEqs()] >>
  PairCases_on `h''` >> gvs[] >>
  simp[AC CONJ_ASSOC CONJ_COMM]
QED
Theorem non_indexed_event_args_exists:
  LENGTH flags = LENGTH tys /\
  LENGTH flags = LENGTH vals ==>
  ?typed_vals.
    non_indexed_event_args flags tys vals = SOME typed_vals /\
    MAP FST typed_vals = log_non_indexed_types flags tys /\
    MAP SND typed_vals = log_non_indexed_values flags vals
Proof
  qid_spec_tac `vals` >> qid_spec_tac `tys` >> Induct_on `flags`
  >- (Cases_on `tys` >> Cases_on `vals` >>
      simp[non_indexed_event_args_def, log_non_indexed_types_def,
           log_non_indexed_values_def])
  >> qx_gen_tac `flag` >> qx_gen_tac `tys` >> qx_gen_tac `vals` >>
  Cases_on `tys` >> Cases_on `vals` >> Cases_on `flag` >>
  gvs[non_indexed_event_args_def, log_non_indexed_types_def,
      log_non_indexed_values_def] >>
  strip_tac >> first_x_assum drule >> disch_then drule >> strip_tac >>
  qexists `(h,h')::typed_vals` >> simp[]
QED


(* RETIRED PROVENANCE: source logs are concrete events. Replacement claims
   log_entry_equiv_concrete_event/log_entry_corresponds_concrete_event below.
   Original symbolic-log proofs retained, not saved or used.
Theorem log_entry_equiv_encode_vyper_event:
  log_entry_equiv cenv addr (eid, vals) ev <=>
  encode_vyper_event cenv.ce_event_info cenv.ce_type_env addr
    (nsid_to_string eid) vals = SOME ev
Proof
  Cases_on `cenv.ce_event_info (nsid_to_string eid)`
  >- simp[log_entry_equiv_def, encode_vyper_event_def]
  >> PairCases_on `x` >>
  simp[log_entry_equiv_def, encode_vyper_event_def,
       encode_vyper_event_metadata_def] >>
  eq_tac
  >- (strip_tac >>
      `encode_indexed_event_topics x2 x1 vals = SOME topic_tail` by
        (simp[encode_indexed_event_topics_characterization] >> metis_tac[]) >>
      `?typed_vals.
         non_indexed_event_args x2 x1 vals = SOME typed_vals /\
         MAP FST typed_vals = log_non_indexed_types x2 x1 /\
         MAP SND typed_vals = log_non_indexed_values x2 vals` by
        (irule non_indexed_event_args_exists >> metis_tac[]) >>
      Cases_on `ev` >> gvs[vfmTypesTheory.event_component_equality])
  >> Cases_on `encode_indexed_event_topics x2 x1 vals`
  >- simp[]
  >> Cases_on `non_indexed_event_args x2 x1 vals`
  >- simp[]
  >> Cases_on `vyper_to_abi_list cenv.ce_type_env (MAP FST x') (MAP SND x')`
  >- simp[]
  >> simp[] >> strip_tac >>
  gvs[encode_indexed_event_topics_characterization,
      non_indexed_event_args_characterization,
      vfmTypesTheory.event_component_equality] >>
  qexists `x` >> simp[]
QED

Theorem log_entry_corresponds_encode:
  log_entry_corresponds event_info tenv addr (eid, vals) ev <=>
  encode_vyper_event event_info tenv addr (nsid_to_string eid) vals = SOME ev
Proof
  simp[log_entry_corresponds_def]
QED
*)

Theorem log_entry_equiv_concrete_event:
  log_entry_equiv cenv addr source_event ev <=> source_event = ev
Proof
  simp[log_entry_equiv_def]
QED

Theorem log_entry_corresponds_concrete_event:
  log_entry_corresponds event_info tenv addr source_event ev <=>
  source_event = ev
Proof
  simp[log_entry_corresponds_def]
QED

Theorem log_entry_equiv_raw_event:
  log_entry_equiv cenv addr (encode_raw_event_values addr topic_vals bytes) ev <=>
  ev = <| logger := addr; topics := MAP event_value_to_word topic_vals;
          data := bytes |>
Proof
  simp[log_entry_equiv_def, encode_raw_event_values_def, encode_raw_event_def,
       EQ_SYM_EQ]
QED

Theorem log_entry_corresponds_raw_event:
  log_entry_corresponds event_info tenv addr
    (encode_raw_event_values addr topic_vals bytes) ev <=>
  ev = <| logger := addr; topics := MAP event_value_to_word topic_vals;
          data := bytes |>
Proof
  simp[log_entry_corresponds_def, encode_raw_event_values_def, encode_raw_event_def,
       EQ_SYM_EQ]
QED

(* Vyper logs correspond to EVM events (ordered, same-length).
   event_info maps event name -> SOME (hash, arg_types, indexed_flags)
   for declared events (from EventDecl with indexed flag). *)
Definition logs_correspond_def:
  logs_correspond event_info tenv (addr : address)
    (vyper_logs : log list) (evm_logs : event list) <=>
    LIST_REL (log_entry_corresponds event_info tenv addr)
      vyper_logs evm_logs
End

(* ===== Frame-aware result: outcomes in, requests compared ONLY on success or halt ===== *)

(* On success or halt, the EVM's final accounts (after processing the
   pending deletions), transient storage and requests agree with the
   source's: equal except at storage bytes the source leaves dead
   (accounts_agree, compileEnv). *)

(* Primitive source/Venom result boundary at one observed storage horizon. *)
Definition external_call_result_rel_def:
  external_call_result_rel H tops ret tx (res, am', rqs) vres <=>
    let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
    case (res, vres) of
      (INL v, Halt ss) =>
        tx_return_bytes tops ret tx v ss.vs_returndata /\
        accounts_agree H cx am'.accounts
          (process_deletions ss.vs_pending_deletions ss.vs_accounts) /\
        transient_agree H cx am'.tStorage ss.vs_transient /\
        logs_correspond (compiled_event_info tops) (type_env tops)
          tx.target am'.logs ss.vs_logs /\
        LIST_REL (request_agree H cx) rqs ss.vs_requests
    | (INR HaltException, Halt ss) =>
        ss.vs_returndata = [] /\
        accounts_agree H cx am'.accounts
          (process_deletions ss.vs_pending_deletions ss.vs_accounts) /\
        transient_agree H cx am'.tStorage ss.vs_transient /\
        logs_correspond (compiled_event_info tops) (type_env tops)
          tx.target am'.logs ss.vs_logs /\
        LIST_REL (request_agree H cx) rqs ss.vs_requests
    | (INR (AssertException s), Abort Revert_abort _) => T
    | (INR (AssertException s), Abort ExHalt_abort _) => (s = "UNREACHABLE")
    | (INR (Error (RevertData _)), Abort Revert_abort _) => T
    | (INR (Error (RuntimeError m)), Abort _ _) => T
    | (INR (Error e), Halt _) => unspecified_behaviour_exempt tops e
    | _ => F
End

(* Fixed slots use distinct observations; absent slots must be irrelevant
   to the observation selected by run. *)
Definition gas_readings_rel_def:
  gas_readings_rel readings run out <=>
    ?slots unused.
      PERM (MAP THE (FILTER IS_SOME slots) ++ unused) readings /\
      !gobs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots gobs ==>
        run (gobs ++ tail) = out
End

Definition call_success_rel_def:
  call_success_rel H tops ret tx (v, am', rqs) es r es' <=>
    let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
    ?out.
      frame_outcome es r es' NONE out am'.logs /\
      tx_return_bytes tops ret tx v out /\
      accounts_agree H cx am'.accounts
        (process_deletions es'.rollback.toDelete es'.rollback.accounts) /\
      transient_agree H cx am'.tStorage es'.rollback.tStorage /\
      LIST_REL (request_agree H cx) rqs (call_requests es)
End

Definition exception_outcome_rel_def:
  (exception_outcome_rel tops (AssertException s) es r es' <=>
     ?exc out lgs.
       frame_outcome es r es' (SOME exc) out lgs /\
       (exc = Reverted \/ s = "UNREACHABLE")) /\
  (exception_outcome_rel tops (Error e) es r es' <=>
     unspecified_behaviour_exempt tops e \/
     ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs) /\
  (exception_outcome_rel tops _ es r es' <=> F)
End

Theorem exception_outcome_rel_cases:
  exception_outcome_rel tops exc es r es' <=>
    case exc of
      AssertException s =>
        ?failure out lgs.
          frame_outcome es r es' (SOME failure) out lgs /\
          (failure = Reverted \/ s = "UNREACHABLE")
    | Error e =>
        unspecified_behaviour_exempt tops e \/
        ?failure out lgs. frame_outcome es r es' (SOME failure) out lgs
    | _ => F
Proof
  Cases_on `exc` >> simp[exception_outcome_rel_def]
QED

(* Fixed-reading transport used by the compiler proof. *)
Definition call_result_rel_at_def:
  call_result_rel_at gobs tops ret am tx es r es' <=>
    let H = storage_trace_horizon
      (source_storage_trace am tx (MAP SND (call_trace es)) gobs) in
    let (res, am', rqs) =
      call_external (SOME (MAP SND (call_trace es))) gobs am tx in
    case res of
      INL v => call_success_rel H tops ret tx (v, am', rqs) es r es'
    | INR HaltException =>
        let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
          frame_outcome es r es' NONE [] am'.logs /\
          accounts_agree H cx am'.accounts
            (process_deletions es'.rollback.toDelete es'.rollback.accounts) /\
          transient_agree H cx am'.tStorage es'.rollback.tStorage /\
          LIST_REL (request_agree H cx) rqs (call_requests es)
    | INR exc => exception_outcome_rel tops exc es r es'
End

Definition call_result_rel_def:
  call_result_rel tops ret am tx es r es' <=>
    gas_readings_rel (gas_readings es)
      (\gobs.
        source_storage_ok am tx (MAP SND (call_trace es)) gobs ∧
        call_outcomes_storage_ok am tx (MAP SND (call_trace es)) gobs ==>
        call_result_rel_at gobs tops ret am tx es r es') T
End
