(* Explicit pre-PLAN-5.5 compatibility contracts. Removal owner TASK056,
   migration owners TASK054/056 (lowering source-unit contract: TASK051).
   These are the OLD definitions, not aliases or bridges to the new boundary.
   In particular NONE-mode semantics, saved-snapshot accounts, unwrapped returns
   and permissive errors are retained solely for existing proved clients.
   No theorem here claims equivalence with e2eDefs' clean boundary. *)
Theory e2eLegacyDefs
Ancestors
  e2eDefs codegenCorrectness passSimulationDefs assemblyFinalizer asmTargetSafety
  compileEnv selectorDispatch vyperInterpreter vyperEntryCompat venomState
  vfmExecution

Definition ctx_transform_correct_legacy_def:
  ctx_transform_correct_legacy R_ok R_term ctx ctx' s <=>
    pass_correct R_ok R_term R_term
      (\fuel. run_context fuel ctx s)
      (\fuel. run_context fuel ctx' s)
End

Definition checked_unit_transform_correct_legacy_def:
  checked_unit_transform_correct_legacy
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    rpolicy R_ok R_term (unit : compilation_unit) s <=>
    ?out. pipeline rpolicy unit = SOME out /\
      ctx_transform_correct_legacy R_ok R_term
        unit.cu_context out.po_unit.cu_context s
End

Definition finalizer_correct_legacy_def:
  finalizer_correct_legacy rpolicy (finalizer : assembly_finalizer) <=>
    !asm finalized_asm.
      finalizer rpolicy asm = SOME finalized_asm ==>
      assembly_target_safe rpolicy.rpol_target finalized_asm /\
      (rpolicy.rpol_final_assembly = FAP_Preserve ==>
       finalized_asm = asm)
End

Definition source_deployment_rel_legacy_def:
  source_deployment_rel_legacy tops am tx cenv <=>
    ?mods. ALOOKUP am.sources tx.target = SOME mods /\
           ALOOKUP mods cenv.ce_module = SOME tops
End

Definition return_data_encodes_legacy_def:
  return_data_encodes_legacy tenv ret_type v es' <=>
    ?abi_val ctxt rb rest.
      es'.contexts = (ctxt, rb) :: rest /\
      vyper_to_abi tenv ret_type v = SOME abi_val /\
      ctxt.returnData =
        enc (vyper_to_abi_type tenv ret_type) abi_val
End

Definition state_effects_match_legacy_def:
  state_effects_match_legacy event_info (addr : address) tenv
    (am' : abstract_machine) es' <=>
    ?ctxt rb rest.
      es'.contexts = (ctxt, rb) :: rest /\
      es'.rollback.accounts = am'.accounts /\
      es'.rollback.tStorage = am'.tStorage /\
      logs_correspond event_info tenv addr am'.logs ctxt.logs
End

Definition state_unchanged_legacy_def:
  state_unchanged_legacy es es' <=>
    es'.rollback.accounts = es.rollback.accounts /\
    es'.rollback.tStorage = es.rollback.tStorage
End

Definition vyper_evm_correspondence_legacy_def:
  vyper_evm_correspondence_legacy tenv event_info ret am tx es <=>
    (case call_external_simple am tx of
       (INL v, am') =>
         ?es'.
           run es = SOME (INR NONE, es') /\
           return_data_encodes_legacy tenv ret v es' /\
           state_effects_match_legacy event_info tx.target tenv am' es'
     | (INR (AssertException _), _) =>
         ?es'. run es = SOME (INR (SOME Reverted), es')
     | (INR (Error _), _) => T
     | (INR BreakException, _) => F
     | (INR ContinueException, _) => F
     | (INR (ReturnException _), _) => F)
End

Definition initial_evm_rel_legacy_def:
  initial_evm_rel_legacy cp bytecode vs es <=>
    initial_codegen_state_rel cp vs /\
    ~NULL es.contexts /\
    let (ctxt, rb) = HD es.contexts in
      rb.accounts = vs.vs_accounts /\
      rb.tStorage = vs.vs_transient /\
      ctxt.returnData = vs.vs_returndata /\
      ctxt.logs = vs.vs_logs /\
      ctxt.stack = [] /\
      (!i. read_byte i vs.vs_memory = read_byte i ctxt.memory) /\
      ctxt.msgParams.data = vs.vs_call_ctx.cc_calldata /\
      ctxt.pc = 0 /\
      ctxt.msgParams.code = bytecode /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
End

Definition valid_function_call_legacy_def:
  valid_function_call_legacy tenv am tx selectors calldata args ret <=>
    (?mut nr dflts body.
       lookup_exported_function
         (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
         tx.function_name = SOME (mut, nr, args, dflts, ret, body)) /\
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args
      calldata /\
    (?sel fn_lbl htz.
       MEM (sel, fn_lbl, htz) selectors /\
       selector_matches sel tx.function_name
         (vyper_to_abi_types tenv (MAP SND args)))
End

(* The local loop is preserved under a legacy name; the clean API uses
   Verifereum's run_call, never this local compatibility definition. *)
Definition run_call_legacy_def:
  run_call_legacy es =
    let depth = LENGTH es.contexts in
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ depth)
           (step o SND)
           (INL (), es)
End

Definition call_state_rel_legacy_def:
  call_state_rel_legacy (program : toplevel list) bytecode am tx tenv
                 (ctxt : context) (rb : rollback_state)
                 (txp : transaction_parameters) ⇔
    ctxt.msgParams.code = bytecode ∧
    ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode ∧
    ctxt.pc = 0 ∧ ctxt.stack = [] ∧ ctxt.logs = [] ∧
    ctxt.returnData = [] ∧ ctxt.memory = [] ∧
    rb.accounts = am.accounts ∧ rb.tStorage = am.tStorage ∧
    ctxt.msgParams.caller = tx.sender ∧
    ctxt.msgParams.callee = tx.target ∧ ctxt.msgParams.value = tx.value ∧
    txp.origin = tx.origin ∧ txp.gasPrice = tx.gas_price ∧
    txp.baseFeePerGas = tx.base_fee ∧ txp.blockNumber = tx.block_number ∧
    txp.blockTimeStamp = tx.time_stamp ∧ txp.blockCoinBase = tx.coinbase ∧
    txp.blockGasLimit = tx.gas_limit ∧ txp.chainId = tx.chain_id ∧
    txp.blobHashes = tx.blob_hashes ∧
    txp.baseFeePerBlobGas = tx.blob_base_fee ∧
    tenv = type_env program ∧
    (∃mods. ALOOKUP am.sources tx.target = SOME mods)
End

Definition valid_vyper_call_legacy_def:
  valid_vyper_call_legacy am tx tenv calldata ret ⇔
    ∃mut nr args dflts body.
      lookup_exported_function
        (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
        tx.function_name = SOME (mut, nr, args, dflts, ret, body) ∧
      calldata_encodes tenv tx.function_name (MAP SND args) tx.args calldata
End

Definition caller_pre_logs_legacy_def:
  caller_pre_logs_legacy [] = ([] : event list) ∧
  caller_pre_logs_legacy (((ctxt : context), rb) :: _) = ctxt.logs
End

Definition call_result_matches_legacy_def:
  call_result_matches_legacy tenv event_info am tx ret r es es_f ⇔
    ∃ctxt_hd rb_hd accts tstor accs tdel md.
    es_f = es with <|
      contexts := (ctxt_hd, rb_hd) :: TL (TL es.contexts);
      rollback := es.rollback with <|
        accounts := accts; tStorage := tstor;
        accesses := accs; toDelete := tdel
      |>;
      msdomain := md
    |> ∧
    case call_external_simple am tx of
      (INL v, am') =>
        (r = INR NONE ∨
         (r = INL () ∧ ¬NULL ctxt_hd.stack ∧ HD ctxt_hd.stack = 1w)) ∧
        return_data_encodes_legacy tenv ret v es_f ∧
        accts = am'.accounts ∧ tstor = am'.tStorage ∧
        (∃evm_logs.
           ctxt_hd.logs = caller_pre_logs_legacy (TL es.contexts) ++ evm_logs ∧
           logs_correspond event_info tenv tx.target am'.logs evm_logs)
    | (INR (AssertException _), _) =>
        r = INR (SOME Reverted) ∨
        (r = INL () ∧ ¬NULL ctxt_hd.stack ∧ HD ctxt_hd.stack = 0w ∧
         accts = am.accounts ∧ tstor = am.tStorage)
    | (INR (Error _), _) => T
    | (INR BreakException, _) => F
    | (INR ContinueException, _) => F
    | (INR (ReturnException _), _) => F
End
