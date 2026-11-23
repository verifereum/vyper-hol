Theory vyperTestRunner
Ancestors
  vyperSmallStepCV
  contractABI vyperABIDecode vyperABI vyperInterpreter vyperSmallStep jsonAST
  jsonToVyper vfmContext vfmExecution vfmTransaction vfmDecreasesGas
  vyperStateCheckpoint vyperCalldata
Libs
  cv_transLib wordsLib

(* TODO(cleanup): move this ABI test-runner representation to contractABITheory
   or another shared ABI support theory. *)

Datatype:
  abi_function = <|
    name: string
  ; inputs: (string # abi_type) list
  ; outputs: (string # abi_type) list
  ; mutability: function_mutability (* TODO(cleanup): not dependent on Vyper. *)
  |>
End

Datatype:
  abi_entry
  = Function abi_function
  | Event string (* TODO(test-semantics): determine whether event argument metadata is needed. *)
  | Error string ((string # abi_type) list)
End

Datatype:
  deployment_trace = <|
    sourceAst: (num option, toplevel list) alist
  ; sourceExports: (string # num) list
  ; importMap: (string # num) list  (* alias or layout module path -> source_id, for storage layout key transform *)
  ; contractAbi: abi_entry list
  ; deployedAddress: address
  ; deployer: address
  ; deploymentSuccess: bool
  ; value: num
  ; timeStamp: num
  ; blockNumber: num
  ; blockHashes: bytes32 list
  ; blobHashes: bytes32 list
  ; blobBaseFee: num
  ; gasPrice: num
  ; chainId: num
  ; initcode: byte list
  ; callData: byte list
  ; runtimeBytecode: byte list
  ; storageLayout: json_storage_layout
  ; isBlueprint: bool
  ; readsGas: bool (* the source reads msg.gas, so calls need GAS readings *)
  |>
End

Datatype:
  raw_deployment_trace = <|
    deployer: address
  (* The deployer's nonce before this deployment, when the export recorded
     it; replay advances the deployer to it. *)
  ; deployerNonce: num option
  ; expectedAddress: address
  ; expectedSuccess: bool
  ; value: num
  ; timeStamp: num
  ; blockNumber: num
  ; blockHashes: bytes32 list
  ; blobHashes: bytes32 list
  ; blobBaseFee: num
  ; gasLimit: num
  ; gasPrice: num
  ; chainId: num
  ; initcode: byte list
  ; callData: byte list
  ; expectedRuntimeBytecode: byte list option
  |>
End

val () = cv_auto_trans extract_storage_layout_def;

Definition compute_selector_names_def:
  compute_selector_names [] = [] ∧
  compute_selector_names (Function x::ls) = (
  let name = x.name in
  let argTypes = MAP SND x.inputs in
  let retTypes = MAP SND x.outputs in
  let sel = function_selector name argTypes in
    (sel, name, argTypes, retTypes)::compute_selector_names ls ) ∧
  compute_selector_names (e::ls) = compute_selector_names ls
End

val () = cv_auto_trans compute_selector_names_def;

Definition find_deploy_function_name_def:
  find_deploy_function_name [] = "__init__" ∧
  find_deploy_function_name ((FunctionDecl Deploy _ _ _ name _ _ _ _)::_) = name ∧
  find_deploy_function_name (_::ts) = find_deploy_function_name ts
End

val () = cv_auto_trans find_deploy_function_name_def;

Definition find_args_by_name_def:
  find_args_by_name n [] = [] ∧
  find_args_by_name n (Function x::ls) =
  (if n = x.name then MAP SND x.inputs else
     find_args_by_name n ls) ∧
  find_args_by_name n (_::ls) =
  find_args_by_name n ls
End

val () = cv_auto_trans find_args_by_name_def;

Datatype:
  call_trace = <|
    sender: address
  ; target: address
  ; callData: byte list
  ; value: num
  ; timeStamp: num
  ; blockNumber: num
  ; blockHashes: bytes32 list
  ; blobHashes: bytes32 list
  ; blobBaseFee: num
  ; gasLimit: num
  ; gasPrice: num
  ; chainId: num
  ; static: bool
  ; expectedOutput: byte list option
  |>
End

Datatype:
  trace
  = Deployment deployment_trace
  | RawDeployment raw_deployment_trace
  | Call call_trace
  | SetBalance address num
  | ClearTransientStorage
  | StateCheckpoint state_checkpoint
End

Definition compute_vyper_args_def:
  compute_vyper_args all_mods ts vis name argTys cd = let
    abiTupTy = Tuple argTys;
    vyTysRet = case lookup_function NONE name vis ts
                of SOME (_,_,args,_,ret,_) => (MAP SND args, ret)
                  | NONE => ([], NoneT);
    vyTys = TAKE (LENGTH argTys) (FST vyTysRet);
    (* Use combined type env from all modules so cross-module types work *)
    tenv = type_env_all_modules all_mods;
    (* Pad calldata with zeros to model EVM semantics: CALLDATALOAD past
       the end of calldata returns zero. We pad to vyper_abi_size_bound,
       which is the maximum encoding size for this type. *)
    bound = vyper_abi_size_bound tenv (TupleT vyTys);
    padded = PAD_RIGHT 0w bound cd;
    (* Argument decoding uses Vyper's lenient ABI decoding (see
       vyperABIDecode): calldata/CODE argument clamps preserve legacy
       wrap-around head arithmetic. *)
    argsOpt = if
      static_length abiTupTy ≤ LENGTH cd ∧
      vyper_abi_valid_enc abiTupTy padded 0
    then let
      abiArgsTup = vyper_abi_dec abiTupTy padded 0;
      vyArgsTup = abi_to_vyper tenv (TupleT vyTys) abiArgsTup;
      vyArgsTv = evaluate_type tenv (TupleT vyTys)
      in OPTION_BIND vyArgsTv
           (λtv. OPTION_BIND vyArgsTup (extract_elements tv))
    else NONE;
  in
    (argsOpt, tenv, SND vyTysRet)
End

(* Keep the logical runner on the original ABI semantics. Only its CV
   implementation uses the unconditionally proved-equivalent fast paths. *)
val () = compute_vyper_args_def
  |> REWRITE_RULE [GSYM (CONJUNCT1 vyper_abi_dec_fast_eq),
                  GSYM (CONJUNCT1 vyper_abi_valid_enc_fast_eq)]
  |> cv_auto_trans;

Definition increment_account_nonce_def:
  increment_account_nonce addr am =
    am with accounts updated_by
      (update_account addr
        ((lookup_account addr am.accounts) with nonce updated_by SUC))
End

val () = increment_account_nonce_def
  |> SRULE [combinTheory.o_DEF, combinTheory.C_DEF]
  |> cv_auto_trans;

(* The runner's verdict when compute_vyper_args rejects a call's or a
   deployment's calldata. The interpreter never runs on it, and no other code
   raises this message. Vyper's entry also reverts on such calldata, so the
   verdict satisfies an expected failure. *)
Definition calldata_rejected_msg_def:
  calldata_rejected_msg = "runner: ABI decoder rejected calldata"
End

val () = cv_auto_trans calldata_rejected_msg_def;

(* The interpreter's own calldata entry (vyperCalldata): selector lookup,
   fallback and argument decoding, as the compiled contract does them.
   The cv translator takes no higher-order functions, so its FIND, EXISTS and
   OPT_MMAP steps are rewritten to the first-order forms below, proved equal. *)
Definition find_selector_def:
  find_selector tenv sel [] = NONE ∧
  find_selector tenv sel ((name,tys)::sigs) =
    if abi_method_id tenv name tys = sel then SOME (name,tys)
    else find_selector tenv sel sigs
End

Theorem find_selector_FIND:
  ∀sigs. find_selector tenv sel sigs =
         FIND (λ(name,tys). abi_method_id tenv name tys = sel) sigs
Proof
  Induct >- simp[find_selector_def, listTheory.FIND_thm] >>
  Cases >> simp[find_selector_def, listTheory.FIND_thm]
QED

Definition has_default_decl_def:
  has_default_decl [] = F ∧
  has_default_decl (t::ts) = (is_default_decl t ∨ has_default_decl ts)
End

Theorem has_default_decl_EXISTS:
  ∀ts. has_default_decl ts = EXISTS is_default_decl ts
Proof
  Induct >> simp[has_default_decl_def]
QED

Theorem OPT_MMAP_evaluate_type:
  OPT_MMAP (evaluate_type tenv) tys = evaluate_types tenv tys []
Proof
  simp[vyperValueTheory.evaluate_types_OPT_MMAP] >>
  Cases_on `OPT_MMAP (evaluate_type tenv) tys` >> simp[]
QED

(* Mutually recursive groups, translated whole before cv_auto_trans meets them. *)
val () = cv_trans tv_abi_dynamic_def;
val () = cv_trans tv_abi_static_size_def;
val () = cv_trans tv_needs_clamp_def;
val () = cv_trans tv_abi_size_def;
(* Byte/word conversions in the big-endian forms vfmTypes translates. *)
val () = cv_auto_trans
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] cd_word_def);
val () = cv_auto_trans
  (REWRITE_RULE [GSYM byteTheory.word_to_bytes_be_def] cd_word_value_def);
val () = cv_auto_trans cd_member_ptr_def;
val cd_decode_pre_def = cv_trans_pre_rec
  "cd_decode_pre cd_decode_elems_pre cd_decode_list_pre"
  (REWRITE_RULE [GSYM vyperMiscTheory.CHR_o_w2n_eq] cd_decode_def)
  (WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
       INL (_,_,t,_) => (cv_size t, 0)
     | INR (INL (_,_,t,_,_,k)) => (cv_size t, cv$c2n k + 1)
     | INR (INR (_,_,ts,_,_)) => (cv_size ts, 0))`
   \\ rw[]
   \\ qspec_then `cv_snd cv_v` assume_tac vyperMiscTheory.cv_size_cv_map_snd_le
   \\ Cases_on `cv_v` \\ gvs[cvTheory.cv_size_def, cvTheory.cv_lt_def, cvTheory.cv_sub_def, cvTheory.c2b_def]
   \\ TRY (rename1 `cv_size (cv_fst fg)` \\ Cases_on `fg`
           \\ gvs[cvTheory.cv_size_def, cvTheory.cv_fst_def]));

(* The preconditions are only the recursive calls'. *)
Theorem cd_decode_pre[cv_pre,local]:
  (∀nat cd t p. cd_decode_pre nat cd t p) ∧
  (∀nat cd t base i k. cd_decode_elems_pre nat cd t base i k) ∧
  (∀nat cd ts p ofs. cd_decode_list_pre nat cd ts p ofs)
Proof
  ho_match_mp_tac cd_decode_ind \\ rw[]
  \\ simp[Once cd_decode_pre_def] \\ rw[] \\ gvs[]
QED

val () = calldata_dispatch_def
  |> REWRITE_RULE [GSYM find_selector_FIND, GSYM has_default_decl_EXISTS,
                   OPT_MMAP_evaluate_type]
  |> cv_auto_trans;

(* The runner's verdict when calldata_dispatch finds no entry for a call's
   calldata: the contract reverts with empty returndata before any function
   body (calldata_dispatch_def). *)
Definition dispatch_rejected_msg_def:
  dispatch_rejected_msg = "calldata_dispatch: no entry"
End

val () = cv_auto_trans dispatch_rejected_msg_def;

(* RuntimeError messages that are Vyper's own run-time failures (reverts the
   language defines), by exact match. Any other RuntimeError is an internal
   error of the interpreter or the runner and fails a test that expects a
   failure. Where each is raised: *)
Definition contract_failure_messages_def:
  contract_failure_messages = [
    (* semantics/vyperValueOperationScript.sml *)
    "bounded_int_op bound"; "bounded_decimal_op"; "Decimal Mul bound";
    "Exp~"; "Div0"; "Mod0"; "ewv bound"; "ewv neg"; "evaluate_slice range";
    "convert uint bound"; "convert int flag bound"; "convert BytesV bound";
    "convert bytes string"; "convert string bytes";
    "convert string string bound"; "Div overflow";
    "convert BytesV uint bound"; "convert BytesV int bound";
    "convert bytes address"; "convert int bound"; "convert int address";
    "convert flag int bound"; "convert flag uint bound";
    "convert decimal int"; "convert decimal uint"; "append overflow";
    (* semantics/vyperContextScript.sml *)
    "AddMod division by zero"; "MulMod division by zero";
    "evaluate_block_hash"; "evaluate_extract32 start";
    "evaluate_extract32 bytesM"; "evaluate_extract32 address clamp";
    "Neg operand bound"; "ECAdd invalid point"; "ECMul invalid point";
    (* semantics/vyperABIScript.sml, abi_decode *)
    "abi_decode invalid"; "abi_decode conversion";
    (* semantics/vyperStateScript.sml *)
    "evaluate_subscripts array_index"; "array fixed oob";
    "array dynamic length oob"; "pop empty storage array";
    "pop empty memory array"; "append full storage array";
    "assign_subscripts array_index"; "array dynamic capacity oob";
    (* check_not_static here, and the static call value check in
       vyperInterpreterScript.sml *)
    "write in static context";
    (* semantics/vyperCreateScript.sml *)
    "create source has no deployable code"; "create address collision";
    "create initcode too large";
    "create insufficient balance or nonce limit"; "create failed";
    (* semantics/vyperInterpreterScript.sml; "call lookup_function" is
       external dispatch finding no function and no __default__ *)
    "not Payable"; "no range"; "For too long"; "send failed";
    "ExtCall target has no code"; "call lookup_function";
    "transfer_value amount"; "nonreentrant lock";
    (* raw_call_evm below: the EVM call reverted *)
    "raw_call_evm reverted";
    calldata_rejected_msg; dispatch_rejected_msg]
End

val () = cv_auto_trans contract_failure_messages_def;

(* Whether an exception satisfies a trace that expects the call or the
   deployment to fail. *)
Definition expected_failure_def:
  expected_failure (AssertException _) = T ∧
  expected_failure (Error (RevertData _)) = T ∧
  expected_failure (Error (RuntimeError msg)) =
    MEM msg contract_failure_messages ∧
  expected_failure _ = F
End

val () = cv_auto_trans expected_failure_def;

Definition run_deployment_def:
  run_deployment am dt = let
    sns = compute_selector_names dt.contractAbi;
    all_mods = annotate_sources_slots dt.storageLayout dt.sourceAst;
    ts = case ALOOKUP all_mods NONE of SOME ts => ts | NONE => [];
    name = find_deploy_function_name ts;
    argTys = find_args_by_name name dt.contractAbi;
    ar = compute_vyper_args all_mods ts Deploy name argTys dt.callData;
    res = case FST ar of NONE => INR (Error $ RuntimeError calldata_rejected_msg)
          | SOME args => let
    tx = <| sender := dt.deployer
          ; target := dt.deployedAddress
          ; function_name := name
          ; args := args
          ; calldata := []
          ; code := dt.initcode ++ dt.callData
          ; value := dt.value
          ; time_stamp := dt.timeStamp
          ; block_number := dt.blockNumber
          ; block_hashes := dt.blockHashes
          ; blob_hashes := dt.blobHashes
          ; blob_base_fee := dt.blobBaseFee
          ; gas_price := dt.gasPrice
          ; chain_id := dt.chainId
          ; is_creation := T
          ; is_static := F
          ; created_in_tx := T
          ; coinbase := 0w
          ; gas_limit := 0
          ; base_fee := 0
          ; prev_randao := 0
          ; origin := dt.deployer |>;
    in case load_contract NONE [] (increment_account_nonce dt.deployedAddress am)
                          tx all_mods dt.sourceExports of
         INL (am', _) => INL am'
       | INR ex => INR ex
  in (sns, res)
End

val () = cv_auto_trans run_deployment_def;

Definition call_trace_txn_def:
  call_trace_txn ct =
    <| sender := ct.sender
     ; target := ct.target
     ; function_name := ""
     ; args := []
     ; calldata := ct.callData
     ; code := []
     ; value := ct.value
     ; time_stamp := ct.timeStamp
     ; block_number := ct.blockNumber
     ; block_hashes := ct.blockHashes
     ; blob_hashes := ct.blobHashes
     ; blob_base_fee := ct.blobBaseFee
     ; gas_price := ct.gasPrice
     ; chain_id := ct.chainId
     ; is_creation := F
     ; is_static := ct.static
     ; created_in_tx := F
     ; coinbase := 0w
     ; gas_limit := ct.gasLimit
     ; base_fee := 0
     ; prev_randao := 0
     ; origin := ct.sender |>
End

val () = cv_auto_trans call_trace_txn_def;

(* One step of the transaction's frame: the word a depth-1 GAS step pushed. *)
Definition frame_gas_reading_def:
  frame_gas_reading acc s (r', s') =
    case (s.contexts, s'.contexts) of
    | ([(c, _)], [(c', _)]) =>
        if c.pc < LENGTH c.msgParams.code ∧
           FLOOKUP c.msgParams.parsed c.pc = SOME Gas ∧ ISL r'
        then (case c'.stack of w :: _ => w :: acc | [] => acc)
        else acc
    | _ => acc
End

(* The words the GAS steps of the transaction's own frame push, in execution
   order.  These are what msg.gas reads in that frame only when every GAS
   step there is a msg.gas: the lowering also emits GAS for a call without
   gas=, a raw_call without gas= and a precompile call, which consume no
   reading in the source semantics. *)
Definition frame_gas_readings_def:
  frame_gas_readings acc (r, s) =
    case r of
    | INR _ => REVERSE acc
    | INL _ =>
        let rs' = step s in
        frame_gas_readings (frame_gas_reading acc s rs') rs'
Termination
  WF_REL_TAC `inv_image ($< LEX ($< LEX $<)) (λ(acc, r, s).
    if ISR r then ((0:num), (0, 0))
    else (1, contexts_weight 0 s.contexts))`
  \\ rpt gen_tac
  \\ mp_tac (Q.SPEC `s` (REWRITE_RULE [decreases_gas_cred_def]
             decreases_gas_cred_step))
  \\ IF_CASES_TAC >- (
    rw [contexts_weight_def, vfmExecutionPropTheory.unused_gas_def]
    \\ gvs [step_def, handle_def, get_current_context_def, bind_def, fail_def]
    \\ gvs [handle_step_def, reraise_def])
  \\ rw []
  \\ fs[pairTheory.LEX_DEF, pairTheory.UNCURRY]
  \\ metis_tac[sumTheory.sum_CASES, sumTheory.ISL, sumTheory.ISR]
End

(* The frame's GAS readings when the call trace runs as a transaction on the
   EVM: same accounts and transient storage, tx gas (capped as for raw
   deployments), intrinsic gas charged.  [] when the transaction is invalid. *)
Definition call_gas_readings_def:
  call_gas_readings am ct =
    let tx = <| from := ct.sender
              ; to := SOME ct.target
              ; data := ct.callData
              ; nonce := (lookup_account ct.sender am.accounts).nonce
              ; value := ct.value
              ; gasLimit := MIN ct.gasLimit (2 ** 24)
              ; gasPrice := ct.gasPrice
              ; accessList := []
              ; blobVersionedHashes := []
              ; maxFeePerBlobGas := NONE
              ; maxFeePerGas := NONE
              ; authorizationList := []
              |> in
    let blk = <| baseFeePerGas := 0
               ; excessBlobGas := ct.blobBaseFee
               ; gasUsed := 0
               ; blobGasUsed := 0
               ; number := ct.blockNumber
               ; timeStamp := ct.timeStamp
               ; coinBase := 0w
               ; gasLimit := tx.gasLimit
               ; prevRandao := 0w
               ; hash := 0w
               ; parentBeaconBlockRoot := 0w
               ; requestsHash := 0w
               ; stateRoot := 0w
               ; withdrawalsRoot := 0w
               ; rlpSize := 0
               ; transactions := []
               ; withdrawals := []
               |> in
    case run_create (Collect empty_domain) F ct.chainId ct.blockHashes blk
                    am.accounts tx of
    | SOME (INR (_, s, NONE)) =>
        frame_gas_readings [] (set_tStorage am.tStorage s)
    | _ => []
End

val () = cv_auto_trans frame_gas_reading_def;

val frame_gas_readings_pre_def =
  cv_trans_pre "frame_gas_readings_pre" frame_gas_readings_def;

Theorem frame_gas_readings_pre[cv_pre]:
  !acc x. frame_gas_readings_pre acc x
Proof
  simp[pairTheory.FORALL_PROD]
  \\ recInduct frame_gas_readings_ind
  \\ rw[]
  \\ rw[Once frame_gas_readings_pre_def]
QED

val () = cv_auto_trans call_gas_readings_def;

(* A call's entry by the trace's Python ABI description: the selector looked
   up in the trace's ABI, the arguments decoded by compute_vyper_args. *)
Definition python_call_entry_def:
  python_call_entry sns all_mods exps cd = let
    fna = case ALOOKUP sns (TAKE 4 cd) of SOME fna => fna
             | NONE => ("__default__", [], []);
    name = FST fna;
    src_id_opt = case exps of NONE => NONE
                 | SOME export_map => ALOOKUP export_map name;
    ts = case ALOOKUP all_mods src_id_opt of
           SOME ts => ts
         | NONE => case ALOOKUP all_mods NONE of SOME ts => ts | _ => [];
  in
    case FST (compute_vyper_args all_mods ts External name (FST (SND fna))
                (DROP 4 cd)) of
      NONE => NONE
    | SOME args => SOME (name, args)
End

val () = cv_auto_trans python_call_entry_def;

(* Whether every signature has the same argument types under tenv as under
   tenv_all. *)
Definition sigs_resolve_same_def:
  sigs_resolve_same tenv tenv_all [] = T ∧
  sigs_resolve_same tenv tenv_all ((name,tys)::sigs) =
    (evaluate_types tenv tys [] = evaluate_types tenv_all tys [] ∧
     sigs_resolve_same tenv tenv_all sigs)
End

val () = cv_auto_trans sigs_resolve_same_def;

(* Whether calldata_dispatch is the contract's entry. It reads only the main
   module: its external functions, and its own type environment. So the
   contract has a main module (a blueprint has none), may import modules but
   exports none of their functions, and every argument type of its external
   functions means the same in the main module's type environment as in all
   modules'. *)
Definition dispatchable_def:
  dispatchable all_mods exps tops ⇔
    IS_SOME (ALOOKUP all_mods NONE) ∧
    (case exps of NONE => T | SOME em => NULL em) ∧
    sigs_resolve_same (type_env tops) (type_env_all_modules all_mods)
      (abi_external_signatures tops)
End

val () = cv_auto_trans dispatchable_def;

(* A call's entry is the interpreter's own (calldata_dispatch) where the
   contract is dispatchable, else the Python path, whose NONE keeps the
   calldata_rejected_msg verdict. *)
Definition run_call_def:
  run_call reads_gas sns am ct = let
    all_mods = case ALOOKUP am.sources ct.target of
                 SOME mods => mods
               | _ => [];
    exps = ALOOKUP am.exports ct.target;
    tops = case ALOOKUP all_mods NONE of SOME ts => ts | _ => [];
    tenv = type_env_all_modules all_mods;
    dispatched = dispatchable all_mods exps tops;
    entry = if dispatched then calldata_dispatch tops ct.callData
            else python_call_entry sns all_mods exps ct.callData;
  in
    case entry of
      NONE => ((INR (Error $ RuntimeError
                       (if dispatched then dispatch_rejected_msg
                        else calldata_rejected_msg)), am),
               (NoneT, (tenv, F)))
    | SOME (name, args) => let
    (* Check exports to find which module the function lives in *)
    src_id_opt = case exps of
                   NONE => NONE
                 | SOME export_map => ALOOKUP export_map name;
    ts = case ALOOKUP all_mods src_id_opt of
           SOME ts => ts
         | NONE => tops;
    retType = case lookup_function NONE name External ts of
                SOME (_,_,_,_,ret,_) => ret
              | NONE => NoneT;
    tx = <| sender := ct.sender
          ; target := ct.target
          ; function_name := name
          ; args := args
          ; calldata := ct.callData
          ; code := (lookup_account ct.target am.accounts).code
          ; value := ct.value
          ; time_stamp := ct.timeStamp
          ; block_number := ct.blockNumber
          ; block_hashes := ct.blockHashes
          ; blob_hashes := ct.blobHashes
          ; blob_base_fee := ct.blobBaseFee
          ; gas_price := ct.gasPrice
          ; chain_id := ct.chainId
          ; is_creation := F
          ; is_static := ct.static
          ; created_in_tx := F
          ; coinbase := 0w
          ; gas_limit := ct.gasLimit
          ; base_fee := 0
          ; prev_randao := 0
          ; origin := ct.sender |>;
    (* TODO(test-semantics): thread additional environment data from the trace. *)
    (* Whether the callee returns raw bytes or an ABI encoding, and hence how
       its EVM returndata must be read back, is decided by the interpreter
       (call_external_raw_return) from the declaration call_external runs. *)
    is_raw = call_external_raw_return am tx;
    gobs = if reads_gas then call_gas_readings am ct else []
  in (let (res, am', _) = call_external NONE gobs am tx in (res, am'),
      (retType, (tenv, is_raw)))
End

val () = cv_auto_trans run_call_def;

Definition raw_call_evm_def:
  raw_call_evm am ct =
    let value_opt = if ct.static then NONE else SOME ct.value in
    let txParams = vyper_to_tx_params (call_trace_txn ct) in
    case run_ext_call ct.sender ct.target ct.callData value_opt default_evm_gas_limit
                      am.accounts am.tStorage txParams of
    | NONE => (INR (Error $ RuntimeError "raw_call_evm"), am)
    | SOME (success, returnData, accounts, tStorage, emitted_logs, deletions) =>
        let am' = am with <| accounts := accounts;
                            tStorage := tStorage;
                            logs updated_by (λls. ls ++ emitted_logs);
                            pending_deletions updated_by (APPEND deletions) |> in
        if success then (INL returnData, finalize_pending_deletions am')
        else (INR (Error $ RuntimeError "raw_call_evm reverted"), am')
End

val () = cv_auto_trans raw_call_evm_def;


Definition make_create_tx_def:
  make_create_tx sender nonce value data gas_limit gas_price : transaction =
    <| from := sender
     ; to := NONE
     ; data := data
     ; nonce := nonce
     ; value := value
     ; gasLimit := MIN gas_limit (2 ** 24)
     ; gasPrice := gas_price
     ; accessList := []
     ; blobVersionedHashes := []
     ; maxFeePerBlobGas := NONE
     ; maxFeePerGas := NONE
     ; authorizationList := []
     |>
End

val () = cv_auto_trans make_create_tx_def;

Definition make_create_block_def:
  make_create_block (dt: raw_deployment_trace) =
    <| baseFeePerGas := 0
     ; excessBlobGas := dt.blobBaseFee
     ; gasUsed := 0
     ; blobGasUsed := 0
     ; number := dt.blockNumber
     ; timeStamp := dt.timeStamp
     ; coinBase := 0w
     ; gasLimit := dt.gasLimit
     ; prevRandao := 0w
     ; hash := 0w
     ; parentBeaconBlockRoot := 0w
     ; requestsHash := 0w
     ; stateRoot := 0w
     ; withdrawalsRoot := 0w
     ; rlpSize := 0
     ; transactions := []
     ; withdrawals := []
     |>
End

val () = cv_auto_trans make_create_block_def;

(* Keep VFM's CREATE admission, intrinsic gas, nonce, fee accounting and
   deletion processing, but retain the transient state that run_transaction's
   result omits.  The pinned py-evm direct CREATE helper neither clears existing
   transient slots nor discards successful initcode writes.  Seed both the live
   and saved rollback states so nested calls and failed creates see the same
   pre-deployment transient world. *)
Definition raw_create_transaction_def:
  raw_create_transaction chainId blockHashes blk accounts tStorage tx =
    case run_create (Collect empty_domain) F chainId blockHashes blk accounts tx of
    | NONE => NONE
    | SOME (INL (tr, accounts)) => SOME (tr, accounts, tStorage)
    | SOME (INR (acc, s, precomp)) =>
        if IS_SOME precomp then NONE else
        let s = s with <|
          rollback updated_by (λrb. rb with tStorage := tStorage);
          contexts updated_by
            (MAP (λ(c, rb). (c, rb with tStorage := tStorage))) |> in
        case vfmExecution$run s of
        | SOME (INR result, s') =>
            let (tr, accounts) = post_transaction_accounting blk tx result acc s' in
            SOME (tr, accounts,
                  if IS_NONE result then s'.rollback.tStorage else tStorage)
        | _ => NONE
End

val () = cv_auto_trans raw_create_transaction_def;

Theorem raw_create_initial_transient[local]:
  initial_state dom static chainId blockHashes blk accounts tx = SOME s ⇒
  s.rollback.tStorage = empty_transient_storage ∧
  MAP (λ(c, rb). (c, rb with tStorage := empty_transient_storage)) s.contexts =
    s.contexts
Proof
  simp[initial_state_def] >>
  Cases_on `pre_transaction_updates accounts
    (base_fee_per_blob_gas blk.excessBlobGas) tx` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[initial_rollback_def]
QED

Theorem raw_create_empty_transient_state[local]:
  tx.to = NONE ∧
  run_create dom static chainId blockHashes blk accounts tx =
    SOME (INR (acc, s, precomp)) ⇒
  precomp = NONE ∧
  s with <|
    rollback updated_by (λrb. rb with tStorage := empty_transient_storage);
    contexts updated_by
      (MAP (λ(c, rb). (c, rb with tStorage := empty_transient_storage))) |> = s
Proof
  strip_tac >> fs[run_create_def] >>
  Cases_on `initial_state dom static chainId blockHashes blk accounts tx` >>
  gvs[] >>
  drule raw_create_initial_transient >> strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[execution_state_component_equality, rollback_state_component_equality]
QED

(* With ordinary transaction-start transient storage, projecting away the
   retained transient result is exactly VFM's transaction executor. *)
Theorem raw_create_transaction_empty_transient:
  tx.to = NONE ⇒
  OPTION_MAP (λ(tr, accounts, tStorage). (tr, accounts))
    (raw_create_transaction chainId blockHashes blk accounts
                            empty_transient_storage tx) =
  run_transaction (Collect empty_domain) F chainId blockHashes blk accounts tx
Proof
  strip_tac >>
  Cases_on `run_create (Collect empty_domain) F chainId blockHashes blk accounts tx` >>
  simp[raw_create_transaction_def, run_transaction_def] >>
  rename1 `run_create _ _ _ _ _ _ _ = SOME creation` >>
  Cases_on `creation` >> gvs[]
  >- (rename1 `run_create _ _ _ _ _ _ _ = SOME (INL terminal)` >>
      PairCases_on `terminal` >> simp[]) >>
  rename1 `run_create _ _ _ _ _ _ _ = SOME (INR pending)` >>
  PairCases_on `pending` >>
  drule_all raw_create_empty_transient_state >> strip_tac >>
  gvs[] >>
  rpt (FIRST [pairarg_tac, CASE_TAC] >> gvs[])
QED

Definition run_raw_deployment_def:
  run_raw_deployment am (dt: raw_deployment_trace) =
    let sender = lookup_account dt.deployer am.accounts in
    let nonce = case dt.deployerNonce of NONE => sender.nonce | SOME n => n in
    let am = am with accounts updated_by
               update_account dt.deployer (sender with nonce := nonce) in
    (* The direct fixture deployment helper executes with gas price zero and
       charges no fees, independently of transaction metadata in the trace. *)
    let tx = make_create_tx dt.deployer nonce dt.value
                            (dt.initcode ++ dt.callData)
                            dt.gasLimit 0 in
    let expected = callee_from_tx_to dt.deployer nonce NONE in
    let blk = make_create_block dt in
    if nonce < sender.nonce then
      INR (Error $ RuntimeError "raw deployment deployer nonce below replay")
    (* Failed deployments may record no address (0w); only check the CREATE
       address when the trace recorded one. *)
    else if dt.expectedAddress <> 0w /\ expected <> dt.expectedAddress then
      INR (Error $ RuntimeError "raw deployment address mismatch")
    (* Direct fixture CREATE consumes its nonce even when the endowment is
       unaffordable. No initcode executes and no transaction gas fee is charged. *)
    else if sender.balance < dt.value then
      if dt.expectedSuccess then
        INR (Error $ RuntimeError "raw deployment success mismatch")
      else INL (increment_account_nonce dt.deployer am)
    else
      case raw_create_transaction dt.chainId dt.blockHashes blk
                                  am.accounts am.tStorage tx of
      | NONE => INR (Error $ RuntimeError "raw deployment run failed")
      | SOME (tr, accounts, tStorage) =>
          let success = IS_NONE tr.result in
          if success <> dt.expectedSuccess then
            INR (Error $ RuntimeError "raw deployment success mismatch")
          else if success then
            let code = (lookup_account dt.expectedAddress accounts).code in
            if case dt.expectedRuntimeBytecode of
               | NONE => F
               | SOME bc => code <> bc
            then INR (Error $ RuntimeError "raw deployment bytecode mismatch")
            else INL (am with <| accounts := accounts;
                                 tStorage := tStorage;
                                 logs updated_by (λls. ls ++ tr.logs) |>)
          else INL (increment_account_nonce dt.deployer am)
End

val () = cv_auto_trans run_raw_deployment_def;

(* The addresses whose account code run_trace copies from the trace (a
   blueprint's or an interpreted deployment's dt.runtimeBytecode) instead of
   computing it: exactly those it adds to snss. That code agrees with the
   trace by construction, so a comparison of the replayed state against the
   trace must leave it out. *)
Definition trace_code_addresses_def:
  trace_code_addresses snss = MAP FST snss
End

Definition run_trace_def:
  run_trace snss am tr =
  case tr
  of Deployment dt =>
    if dt.isBlueprint then
      (* Blueprint deployment: just store bytecode, no constructor *)
      let am' = am with accounts updated_by
            (update_account dt.deployedAddress
              ((lookup_account dt.deployedAddress am.accounts)
                with <| code := dt.runtimeBytecode; nonce := 1 |>)) in
      ((dt.deployedAddress,(F,[]))::snss, INL (increment_account_nonce dt.deployer am'))
    else let
      (s_layout, t_layout) = extract_storage_layout dt.importMap dt.storageLayout;
      am_with_layout = am with layouts updated_by CONS (dt.deployedAddress, (s_layout, t_layout));
      result = run_deployment am_with_layout dt;
      sns = FST result; res = SND result;
      res = if dt.deploymentSuccess then
              (* Set the bytecode in accounts after successful deployment *)
              case res of
                INL am' => if IS_NONE (ALOOKUP am'.sources dt.deployedAddress)
                  then INL am'
                  else INL (am' with
                  accounts updated_by
                    (update_account dt.deployedAddress
                      ((lookup_account dt.deployedAddress am'.accounts)
                        with code := dt.runtimeBytecode)))
              | err => err
            else (case res of
                  | INR ex => if expected_failure ex then INL am else INR ex
                  | INL _ => INR (Error $ RuntimeError "deployment success"));
      res = case res of
              INL am' => INL (increment_account_nonce dt.deployer am')
            | INR e => INR e;
      snss = (case res of
                INL am' =>
                  if IS_SOME (ALOOKUP am'.sources dt.deployedAddress)
                  then (dt.deployedAddress,(dt.readsGas,sns))::snss else snss
              | INR _ => snss);
    in
      (snss, res)
   | RawDeployment dt =>
     (snss, run_raw_deployment am dt)
   | StateCheckpoint cp => (snss,
       case compare_state_checkpoint (trace_code_addresses snss) am cp of
       | NONE => INL am
       | SOME message => INR (Error (RuntimeError message)))
   | ClearTransientStorage => (snss,
       INL (am with tStorage := empty_transient_storage))
   | SetBalance addr bal => (snss,
       INL (am with accounts updated_by
            (update_account addr
             ((lookup_account addr am.accounts) with balance := bal)))
     )
   | Call ct => (snss,
     case ALOOKUP snss ct.target
     of NONE =>
        (* Exported calls are message calls: preserve the sender nonce and
           execute any raw-deployed fallback, even with empty calldata. *)
        (let rr = raw_call_evm am ct in
         let res = FST rr; am' = SND rr in
         case res of
         | INR ex =>
             if IS_NONE ct.expectedOutput ∧ expected_failure ex
             then INL am' else INR ex
         | INL out =>
             (case ct.expectedOutput of
              | NONE => INR (Error $ RuntimeError "error expected")
              | SOME expected =>
                  if out = expected then INL am'
                  else INR (Error $ RuntimeError "output mismatch")))
      | SOME (reads_gas, sns) => let
        cr = run_call reads_gas sns am ct;
        call_res = FST cr;
        am = SND call_res in
       case FST call_res
       of
        | INR HaltException =>
            if ct.expectedOutput = SOME [] then INL am
            else INR (Error $ RuntimeError "halt output mismatch")
       | INR ex => if IS_NONE ct.expectedOutput ∧ expected_failure ex
                   then INL am else INR ex
       | INL v =>
       case ct.expectedOutput
         of NONE => INR (Error $ RuntimeError "error expected")
          | SOME out => let
              ar = SND cr;
              rawVyRetTy = FST ar; tenv = FST (SND ar);
              is_raw = SND (SND ar);
            in
              if external_returndata_agrees is_raw tenv rawVyRetTy v out
              then INL am
              else INR (Error $ RuntimeError "output mismatch"))
End

val () = cv_auto_trans run_trace_def;

Definition run_test_loop_def:
  run_test_loop snss am [] = INL () ∧
  run_test_loop snss am (tr::trs) =
  case run_trace snss am tr of
       (snss, INL am) => run_test_loop snss am trs
     | (_, INR ex) => INR ex
End

val () = cv_auto_trans run_test_loop_def;

Definition run_test_def:
  run_test trs = run_test_loop []
    initial_machine_state trs
End

val () = cv_auto_trans run_test_def;

Definition run_tests_def:
  run_tests ts = MAP run_test ts
End

val () = cv_auto_trans run_tests_def;
