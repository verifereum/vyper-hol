(* PLAN 5.5 boundary, not a compiler correctness certificate.
 * TOP-LEVEL: layouts_agree, source_deployment_rel, source_typing_ok,
 * source_storage_ok, call_outcomes_ok, tx_env_ok, tx_block_fields_rel,
 * value_transfer_ok, accounts_after_transfer, call_state_rel,
 * valid_vyper_call, compiled_event_info, return_bytes,
 * decode_strictness_exempt, source_exempt, call_result_rel, logs_correspond.
 * TASK056: all compiler/call consumers use this exact boundary; the obsolete
 * compatibility owner is deleted. No old/new equivalence is claimed.
 * DAG: source/typing/storage + supported syntax + frame/trace -> e2eDefs;
 * e2eDefs -> entry/producers/composition -> e2eCorrectness.
 *)
Theory e2eDefs
Ancestors
  vfmExecution vfmExecutionProp vfmState
  frameOutcome callTrace
  vyperABI vyperEvent vyperInterpreter
  vyperTypeContract vyperTypeContractSoundness vyperTypeInitialState
  vyperStorageLayoutSafety vyperRuntimeAccounts
  supportedProgram compileEnv selectorDispatch

(* ===== Source deployment, typing and storage ===== *)

Definition layouts_agree_def:
  layouts_agree tops am tx <=>
    let (sl, tl) = (case ALOOKUP am.layouts tx.target of
                      SOME p => p | NONE => ([], [])) in
      (!vis id ty n. MEM (VariableDecl vis Storage id ty (SOME n)) tops ==>
                     ALOOKUP sl (NONE, id) = SOME n) /\
      (!vis id ty n. MEM (VariableDecl vis Transient id ty (SOME n)) tops ==>
                     ALOOKUP tl (NONE, id) = SOME n) /\
      (!vis id kt vt n. MEM (HashMapDecl vis F id kt vt (SOME n)) tops ==>
                        ALOOKUP sl (NONE, id) = SOME n)
End

Definition source_deployment_rel_def:
  source_deployment_rel tops am tx <=>
    ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
    ALOOKUP am.exports tx.target = NONE /\
    layouts_agree tops am tx
End

Definition source_typing_ok_def:
  source_typing_ok tops am tx <=>
    ?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
          checked_contract_runtime_ready art [(NONE, tops)] am tx /\
          machine_well_typed am /\ call_tx_well_typed tx
End

Definition source_storage_ok_def:
  source_storage_ok (tops : toplevel list) am tx <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
      contract_storage_well_formed cx (initial_state am []) /\
      storage_layout_safe cx
End

Definition call_outcomes_ok_def:
  call_outcomes_ok (tops : toplevel list) am tx os <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
      EVERY (\outcome. outcome.co_success ==>
                 accounts_runtime_well_typed outcome.co_accounts /\
                 contract_storage_well_formed cx
                   (initial_state (am with <| accounts := outcome.co_accounts;
                                              tStorage := outcome.co_tStorage |>) []))
            os
End

(* ===== Transaction environment and entry transfer ===== *)

Definition tx_env_ok_def:
  tx_env_ok tx <=>
    tx.block_number <> 0 /\ tx.block_number < 2 ** 255 /\
    MIN 256 tx.block_number <= LENGTH tx.block_hashes /\
    LENGTH tx.block_hashes <= 256
End

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

Definition call_state_rel_def:
  call_state_rel tops runtime_bc am tx es <=>
    ?ctxt rb rest.
      es.contexts = (ctxt, rb) :: rest /\
      wf_state es /\ (?d. es.msdomain = Collect d) /\
      ctxt.jumpDest = NONE /\ ~ctxt.msgParams.static /\
      (?mr. ctxt.msgParams.outputTo = Memory mr) /\
      ctxt.msgParams.code = runtime_bc /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY runtime_bc /\
      LENGTH runtime_bc <= 24576 /\
      ctxt.pc = 0 /\ ctxt.stack = [] /\ ctxt.logs = [] /\
      ctxt.returnData = [] /\ ctxt.memory = [] /\
      value_transfer_ok tx am.accounts /\
      es.rollback.accounts = accounts_after_transfer tx am.accounts /\
      es.rollback.tStorage = am.tStorage /\ am.logs = [] /\
      ctxt.msgParams.caller = tx.sender /\ ctxt.msgParams.callee = tx.target /\
      ctxt.msgParams.value = tx.value /\
      tx_block_fields_rel tx es.txParams /\
      source_deployment_rel tops am tx
End

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

Definition decode_strictness_exempt_def:
  decode_strictness_exempt tops e <=>
    e = RuntimeError "abi_decode invalid" /\
    ?ty. occurs_abi_decode_target ty tops /\
         is_dynamic (vyper_to_abi_type (type_env tops) ty)
End

Definition source_exempt_def:
  source_exempt tops (src : (value + exception) # abstract_machine # call_request list) <=>
    case FST src of INR (Error e) => decode_strictness_exempt tops e | _ => F
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
  encode_event_topic is_bytestring v = SOME topic <=>
  log_topic_equiv is_bytestring v topic
Proof
  Cases_on `is_bytestring` >> Cases_on `v` >>
  simp[encode_event_topic_def, log_topic_equiv_def,
       log_bytestring_topic_def, event_value_to_word_eq_val_to_w256,
       byteTheory.word_of_bytes_be_def] >>
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

(* Vyper logs correspond to EVM events (ordered, same-length).
   event_info maps event name -> SOME (hash, arg_types, indexed_flags)
   for declared events (from EventDecl with indexed flag). *)
Definition logs_correspond_def:
  logs_correspond event_info tenv (addr : address)
    (vyper_logs : log list) (evm_logs : event list) <=>
    LIST_REL (log_entry_corresponds event_info tenv addr)
      vyper_logs evm_logs
End

(* ===== Frame-aware result: outcomes in, requests compared ONLY on success ===== *)

Definition call_result_rel_def:
  call_result_rel tops ret am tx es r es' <=>
    let trace = call_trace es in
    case call_external (SOME (MAP SND trace)) am tx of
      (INL v, am', rqs) =>
        ?out lgs.
          frame_outcome es r es' NONE out lgs /\
          return_bytes tops ret v out /\
          es'.rollback.accounts = am'.accounts /\
          es'.rollback.tStorage = am'.tStorage /\
          logs_correspond (compiled_event_info tops) (type_env tops)
            tx.target am'.logs lgs /\
          rqs = MAP FST trace
    | (INR (AssertException s), _, _) =>
        ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                      (exc = Reverted \/ s = "UNREACHABLE")
    | (INR (Error e), _, _) =>
        decode_strictness_exempt tops e \/
        ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
    | (INR BreakException, _, _) => F
    | (INR ContinueException, _, _) => F
    | (INR (ReturnException _), _, _) => F
End
