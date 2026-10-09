(* Focused PLAN 5.5 contract checks, not a satisfiability/correctness producer.
   In particular no run_call trace correctness or S1-S3 is assumed here. *)
Theory e2eBoundaryTest
Ancestors
  e2eDefs frameOutcome callTrace
  vyperInterpreter vyperContext vyperState vyperABI vyperAST vyperValue
  vyperTypeContractSoundness vyperTypeInitialState vyperTypeContract
  vyperStorageLayoutSafety vyperRuntimeAccounts
  supportedProgram supportedDecls contractABI selectorDispatch
  vfmState[ignore_grammar] vfmExecution[ignore_grammar]
  list alist option pair words
Libs wordsLib

val _ = Parse.hide "body";

(* ===== Entry transfer is the actual source operation ===== *)
Theorem entry_transfer_source_effect:
  value_transfer_ok tx st.accounts ==>
  vyperInterpreter$transfer_value tx.sender tx.target tx.value st =
    (INL (), st with accounts := accounts_after_transfer tx st.accounts)
Proof
  rw[value_transfer_ok_def, accounts_after_transfer_def,
     vyperInterpreterTheory.transfer_value_def,
     vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
     vyperStateTheory.return_def, vyperStateTheory.get_accounts_def,
     vyperStateTheory.check_def, vyperStateTheory.assert_def,
     vyperStateTheory.update_accounts_def] >>
  gvs[evaluation_state_component_equality]
QED

Theorem entry_transfer_degenerate:
  (tx.value = 0 \/ tx.sender = tx.target) ==>
  value_transfer_ok tx accounts /\ accounts_after_transfer tx accounts = accounts
Proof
  simp[value_transfer_ok_def, accounts_after_transfer_def] >> metis_tac[]
QED

Theorem entry_transfer_balance_bounds:
  tx.value <> 0 /\ tx.sender <> tx.target ==>
  (value_transfer_ok tx accounts <=>
    tx.value <= (lookup_account tx.sender accounts).balance /\
    (lookup_account tx.target accounts).balance + tx.value < 2 ** 256)
Proof
  simp[value_transfer_ok_def]
QED

(* One combined observation, not a per-field projection API. The saved
   snapshot rb is deliberately unconstrained by the account equality. *)
Theorem boundary_live_and_fresh:
  call_state_rel tops code am tx es ==>
  es.rollback.accounts = accounts_after_transfer tx am.accounts /\
  es.rollback.tStorage = am.tStorage /\ am.logs = [] /\
  source_deployment_rel tops am tx /\ tx_block_fields_rel tx es.txParams /\
  ?ctxt rb rest.
    es.contexts = (ctxt,rb)::rest /\
    ~ctxt.msgParams.static /\ ctxt.jumpDest = NONE /\
    ctxt.pc = 0 /\ ctxt.stack = [] /\ ctxt.logs = [] /\
    ctxt.memory = [] /\ ctxt.returnData = [] /\
    ctxt.msgParams.code = code /\
    ctxt.msgParams.parsed = parse_code 0 FEMPTY code /\ LENGTH code <= 24576
Proof
  simp[call_state_rel_def] >> metis_tac[]
QED

Theorem block_environment_bounds:
  tx_block_fields_rel tx tp ==>
  tx.block_number <> 0 /\ tx.block_number < 2 ** 255 /\
  MIN 256 tx.block_number <= LENGTH tx.block_hashes /\
  LENGTH tx.block_hashes <= 256 /\
  tp.prevRandao = n2w tx.prev_randao /\ tp.prevHashes = tx.block_hashes
Proof
  simp[tx_block_fields_rel_def, tx_env_ok_def]
QED

Theorem no_genesis_or_unbounded_hash_environment:
  ~tx_env_ok (tx with block_number := 0) /\
  ~tx_env_ok (tx with block_number := 2 ** 255) /\
  (LENGTH hashes > 256 ==> ~tx_env_ok (tx with block_hashes := hashes)) /\
  (MIN 256 tx.block_number > LENGTH hashes ==>
    ~tx_env_ok (tx with block_hashes := hashes))
Proof
  simp[tx_env_ok_def, arithmeticTheory.MIN_DEF] >> rw[] >> decide_tac
QED

(* ===== Exact source module/layout and independent hypotheses ===== *)
Theorem deployed_main_module_exact:
  source_deployment_rel tops am tx <=>
  ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
  ALOOKUP am.exports tx.target = NONE /\ layouts_agree tops am tx
Proof
  simp[source_deployment_rel_def]
QED

Theorem declared_layout_slots:
  layouts_agree
    [VariableDecl Private Storage "s" ty (SOME 7);
     VariableDecl Private Transient "t" ty (SOME 9);
     HashMapDecl Private F "m" kt (Type ty) (SOME 11)] am tx <=>
  let (sl,tl) = case ALOOKUP am.layouts tx.target of
                 NONE => ([],[]) | SOME p => p in
    ALOOKUP sl (NONE,"s") = SOME 7 /\
    ALOOKUP tl (NONE,"t") = SOME 9 /\
    ALOOKUP sl (NONE,"m") = SOME 11
Proof
  simp[layouts_agree_def] >>
  Cases_on `ALOOKUP am.layouts tx.target` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

Theorem typing_and_storage_contracts:
  (source_typing_ok tops am tx <=>
    ?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
          checked_contract_runtime_ready art [(NONE,tops)] am tx /\
          machine_well_typed am /\ call_tx_well_typed tx) /\
  (source_storage_ok tops am tx <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
      contract_storage_well_formed cx (initial_state am []) /\
      storage_layout_safe cx)
Proof
  simp[source_typing_ok_def, source_storage_ok_def]
QED

Theorem outcome_guard_success_only:
  call_outcomes_ok tops am tx [] /\
  call_outcomes_ok tops am tx [co with co_success := F] /\
  (call_outcomes_ok tops am tx [co with co_success := T] <=>
    accounts_runtime_well_typed co.co_accounts /\
    contract_storage_well_formed
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state (am with <|accounts := co.co_accounts;
                               tStorage := co.co_tStorage|>) [])) /\
  (call_outcomes_ok tops am tx (xs ++ ys) <=>
    call_outcomes_ok tops am tx xs /\ call_outcomes_ok tops am tx ys)
Proof
  simp[call_outcomes_ok_def, EVERY_APPEND]
QED

(* ===== Exact lookup/bind; no default/fallback relaxation ===== *)
Theorem valid_call_exact_arguments:
  valid_vyper_call tops tx calldata ret ==>
  tx.function_name <> "__default__" /\
  ?mut args body.
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,body) /\
    LENGTH tx.args = LENGTH args /\
    IS_SOME (bind_arguments (type_env tops) args tx.args) /\
    calldata_encodes (type_env tops) tx.function_name (MAP SND args)
      tx.args calldata
Proof
  simp[valid_vyper_call_def] >> metis_tac[]
QED

Theorem fallback_not_valid_call:
  ~valid_vyper_call tops (tx with function_name := "__default__") calldata ret
Proof
  simp[valid_vyper_call_def]
QED

Theorem invalid_entry_shapes_rejected:
  ~valid_vyper_call
    [FunctionDecl External Nonpayable F F "f" [("a",BaseT (UintT 256))] [] NoneT []]
    (empty_call_txn with function_name := "f") calldata ret /\
  ~valid_vyper_call
    [FunctionDecl External Nonpayable F F "f" [("a",BaseT (UintT 256))]
      [Literal (BaseT (UintT 256)) (IntL 1)] NoneT []]
    (empty_call_txn with <|function_name := "f"; args := [IntV 1]|>) calldata ret /\
  ~valid_vyper_call
    [FunctionDecl External Nonpayable T F "f" [] [] NoneT []]
    (empty_call_txn with function_name := "f") calldata ret /\
  ~valid_vyper_call
    [FunctionDecl External Nonpayable F F "f" [("a",BaseT (UintT 256))] [] NoneT []]
    (empty_call_txn with <|function_name := "f"; args := [BoolV T]|>) calldata ret
Proof
  simp[valid_vyper_call_def, vyperInterpreterTheory.lookup_function_def,
       empty_call_txn_def, bind_arguments_def, vyperValueTheory.evaluate_type_def,
       vyperValueOperationTheory.safe_cast_def]
QED

(* Closed ambiguity check: PLAN's source lookup includes getters, but the
   independent supported whitelist rejects public variables. Do not silently
   strengthen the exact PLAN predicate with an extra MEM FunctionDecl guard. *)
Theorem source_lookup_getter_outside_supported:
  let tops = [VariableDecl Public Storage "g" (BaseT (UintT 256)) (SOME 0)] in
    vyperInterpreter$lookup_function NONE "g" External tops =
      SOME (View,F,[],[],BaseT (UintT 256),
        [Return (SOME (TopLevelName (BaseT (UintT 256)) (NONE,"g")))]) /\
    ~supported_program tops
Proof
  simp[vyperInterpreterTheory.lookup_function_def,
       supported_program_def, supported_declaration_headers_def,
       supported_public_variables_rejected]
QED

(* ===== Canonical external ABI wrapping ===== *)
Theorem no_return_is_empty:
  return_bytes tops NoneT v out <=> out = []
Proof
  simp[return_bytes_def]
QED

Theorem dynamic_return_is_wrapped:
  return_bytes tops (BaseT (StringT 16)) (StringV "a") out <=>
  out = enc (Tuple [String]) (ListV [contractABI$BytesV [97w]])
Proof
  simp[return_bytes_def, needs_external_call_wrap_def] >> EVAL_TAC
QED

Theorem multi_tuple_return_is_unwrapped:
  return_bytes tops (TupleT [BaseT (UintT 256);BaseT BoolT])
    (ArrayV (TupleV [IntV 7;BoolV T])) out <=>
  out = enc (Tuple [Uint 256;Bool]) (ListV [NumV 7;NumV 1])
Proof
  simp[return_bytes_def, needs_external_call_wrap_def]
QED

Theorem singleton_tuple_return_is_wrapped:
  return_bytes tops (TupleT [BaseT (StringT 16)])
    (ArrayV (TupleV [StringV "a"])) out <=>
  out = enc (Tuple [Tuple [String]])
    (ListV [ListV [contractABI$BytesV [97w]]])
Proof
  simp[return_bytes_def, needs_external_call_wrap_def] >> EVAL_TAC
QED

Theorem dynamic_wrapping_differs_from_unwrapped_encoding:
  enc (Tuple [String]) (ListV [contractABI$BytesV [97w]]) <>
  enc String (contractABI$BytesV [97w])
Proof
  EVAL_TAC
QED

Theorem logs_are_ordered_concrete_events:
  logs_correspond info tenv addr source_logs evm_logs <=> source_logs = evm_logs
Proof
  `log_entry_corresponds info tenv addr = $=` by
    simp[FUN_EQ_THM, log_entry_corresponds_def] >>
  simp[logs_correspond_def, LIST_REL_eq]
QED

(* ===== Dynamic strictness: exact error only ===== *)
Definition dynamic_decode_program_def:
  dynamic_decode_program = [FunctionDecl External View F F "decode" [] [] NoneT
    [Expr (TypeBuiltin (BaseT (StringT 16)) (AbiDecode F)
      (BaseT (StringT 16)) [Literal (BaseT (BytesT (Dynamic 96))) (BytesL [])])]]
End

Theorem decoding_exemption_exact:
  (decode_strictness_exempt dynamic_decode_program e <=>
    e = RuntimeError "abi_decode invalid") /\
  ~decode_strictness_exempt [] (RuntimeError "abi_decode invalid") /\
  ~decode_strictness_exempt dynamic_decode_program (RuntimeError "abi_decode conversion") /\
  ~decode_strictness_exempt dynamic_decode_program (TypeError "abi_decode invalid")
Proof
  simp[decode_strictness_exempt_def, occurs_abi_decode_target_def,
    declaration_abi_decode_target_def, dynamic_decode_program_def,
    supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
    supportedExprTraverseTheory.supported_expr_exists_def,
    expr_abi_decode_target_root_def] >>
  qexists_tac `BaseT (StringT 16)` >> simp[]
QED

Theorem static_decode_does_not_exempt_invalid:
  ~decode_strictness_exempt
    [FunctionDecl External View F F "decode" [] [] NoneT
      [Expr (TypeBuiltin (BaseT (UintT 256)) (AbiDecode F)
        (BaseT (UintT 256)) [Literal (BaseT (BytesT (Dynamic 32))) (BytesL [])])]]
    (RuntimeError "abi_decode invalid")
Proof
  simp[decode_strictness_exempt_def, occurs_abi_decode_target_def,
    declaration_abi_decode_target_def,
    supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
    supportedExprTraverseTheory.supported_expr_exists_def,
    expr_abi_decode_target_root_def]
QED

Theorem source_exemption_triple:
  (source_exempt tops (INR (Error e),am,rqs) <=> decode_strictness_exempt tops e) /\
  ~source_exempt tops (INL v,am,rqs) /\
  ~source_exempt tops (INR (AssertException s),am,rqs) /\
  ~source_exempt tops (INR BreakException,am,rqs) /\
  ~source_exempt tops (INR ContinueException,am,rqs) /\
  ~source_exempt tops (INR (ReturnException v),am,rqs)
Proof
  simp[source_exempt_def]
QED

(* ===== Result cases: success REQUESTS, not remaining OUTCOMES ===== *)
Theorem success_requires_requests_and_effects:
  call_external (SOME (MAP SND (call_trace es))) am tx = (INL v,am',rqs) ==>
  (call_result_rel tops ret am tx es r es' <=>
    ?out lgs. frame_outcome es r es' NONE out lgs /\
      return_bytes tops ret v out /\
      es'.rollback.accounts = am'.accounts /\ es'.rollback.tStorage = am'.tStorage /\
      logs_correspond (compiled_event_info tops) (type_env tops) tx.target am'.logs lgs /\
      rqs = MAP FST (call_trace es))
Proof
  simp[call_result_rel_def]
QED

Theorem assert_result_does_not_compare_requests:
  call_external (SOME (MAP SND (call_trace es))) am tx =
    (INR (AssertException s),am',rqs) ==>
  (call_result_rel tops ret am tx es r es' <=>
    ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
      (exc = Reverted \/ s = "UNREACHABLE"))
Proof
  simp[call_result_rel_def]
QED

Theorem error_result_only_exact_exemption_or_failure:
  call_external (SOME (MAP SND (call_trace es))) am tx = (INR (Error e),am',rqs) ==>
  (call_result_rel tops ret am tx es r es' <=>
    decode_strictness_exempt tops e \/
    ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs)
Proof
  simp[call_result_rel_def]
QED

Theorem escaped_control_is_not_related:
  (call_external (SOME (MAP SND (call_trace es))) am tx =
     (INR BreakException,am',rqs) ==>
     ~call_result_rel tops ret am tx es r es') /\
  (call_external (SOME (MAP SND (call_trace es))) am tx =
     (INR ContinueException,am',rqs) ==>
     ~call_result_rel tops ret am tx es r es') /\
  (call_external (SOME (MAP SND (call_trace es))) am tx =
     (INR (ReturnException v),am',rqs) ==>
     ~call_result_rel tops ret am tx es r es')
Proof
  simp[call_result_rel_def]
QED
