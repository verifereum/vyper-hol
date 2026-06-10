Theory evalCompilerRuntime
Ancestors
  byte contractABI finite_map finite_set integer list option pair
  vyperABI vyperAST vyperContext vyperInterpreter vyperValue words
  vfmConstants vfmContext vfmExecution vfmOperation vfmState vfmTransaction
  vfmTypes vfmCompute[ignore_grammar]
Libs
  cv_transLib evalCompilerBytecodeLib finite_mapLib wordsLib

(* TOP-LEVEL:
 *   run_runtime_steps       -- execute bytecode in a minimal single-frame state
 *   run_runtime_steps_from  -- same, with an explicit initial program counter
 *   direct_return_arg_runtime_call
 *                           -- parametric calldata-to-return runtime check
 *   direct_return_arg_source_runtime_equiv
 *                           -- source fixture agrees with runtime
 *)

Definition runtime_caller_def:
  runtime_caller : address = 0x1000w
End

val () = cv_auto_trans runtime_caller_def;

Definition runtime_contract_def:
  runtime_contract : address = 0x2000w
End

val () = cv_auto_trans runtime_contract_def;

Definition runtime_accesses_def:
  runtime_accesses : access_sets =
    <| addresses := fEMPTY; storageKeys := fEMPTY |>
End

val () = cv_auto_trans runtime_accesses_def;

Definition runtime_rollback_def:
  runtime_rollback : rollback_state =
    <| accounts := empty_accounts;
       tStorage := empty_transient_storage;
       accesses := runtime_accesses;
       toDelete := []
    |>
End

val () = cv_auto_trans runtime_rollback_def;

Definition runtime_tx_params_def:
  runtime_tx_params : transaction_parameters =
    <| origin := runtime_caller;
       gasPrice := 0;
       baseFeePerGas := 0;
       baseFeePerBlobGas := 0;
       blockNumber := 0;
       blockTimeStamp := 0;
       blockCoinBase := 0w;
       blockGasLimit := 1000000;
       prevRandao := 0w;
       prevHashes := [];
       blobHashes := [];
       chainId := 1;
       authRefund := 0
    |>
End

val () = cv_auto_trans runtime_tx_params_def;

Definition runtime_msg_params_def:
  runtime_msg_params code calldata : message_parameters =
    <| caller := runtime_caller;
       callee := runtime_contract;
       code := code;
       parsed := parse_code 0 FEMPTY code;
       value := 0;
       gasLimit := 1000000;
       data := calldata;
       static := F;
       outputTo := empty_return_destination
    |>
End

val () = cv_auto_trans runtime_msg_params_def;

Definition runtime_context_def:
  runtime_context code calldata : context =
    <| stack := [];
       memory := [];
       pc := 0;
       jumpDest := NONE;
       returnData := [];
       gasUsed := 0;
       addRefund := 0;
       subRefund := 0;
       logs := [];
       msgParams := runtime_msg_params code calldata
    |>
End

val () = cv_auto_trans runtime_context_def;

Definition runtime_context_at_def:
  runtime_context_at pc code calldata : context =
    (runtime_context code calldata) with pc := pc
End

val () = cv_auto_trans runtime_context_at_def;

Definition runtime_state_at_def:
  runtime_state_at pc code calldata : execution_state =
    <| contexts := [(runtime_context_at pc code calldata, runtime_rollback)];
       txParams := runtime_tx_params;
       rollback := runtime_rollback;
       msdomain := Collect empty_domain
    |>
End

val () = cv_auto_trans runtime_state_at_def;

Definition runtime_state_def:
  runtime_state code calldata = runtime_state_at 0 code calldata
End

val () = cv_auto_trans runtime_state_def;

Definition runtime_context_with_def:
  runtime_context_with pc stack memory returnData gasUsed code calldata =
    (runtime_context_at pc code calldata) with
      <| stack := stack; memory := memory;
         returnData := returnData; gasUsed := gasUsed |>
End

Definition runtime_state_with_def:
  runtime_state_with pc stack memory returnData gasUsed code calldata =
    <| contexts :=
         [(runtime_context_with pc stack memory returnData gasUsed code calldata,
           runtime_rollback)];
       txParams := runtime_tx_params;
       rollback := runtime_rollback;
       msdomain := Collect empty_domain
    |>
End

Theorem runtime_state_at_0:
  runtime_state_at 0 code calldata =
    runtime_state_with 0 [] [] [] 0 code calldata
Proof
  simp[runtime_state_at_def, runtime_state_with_def, runtime_context_with_def,
       runtime_context_at_def, runtime_context_def]
QED

Definition run_steps_def:
  run_steps 0 s = NONE ∧
  run_steps (SUC fuel) s =
    case step s of
      (INL _, s') => run_steps fuel s'
    | (INR result, s') => SOME (result, s')
End

val () = cv_auto_trans run_steps_def;

val run_steps_compute_thm = DB.fetch "-" "run_steps_compute";

Definition run_runtime_steps_from_def:
  run_runtime_steps_from fuel pc code calldata =
    case run_steps fuel (runtime_state_at pc code calldata) of
      NONE => NONE
    | SOME (result, s) =>
        case s.contexts of
          [] => SOME (result, [])
        | (ctxt, _) :: _ => SOME (result, ctxt.returnData)
End

val () = cv_auto_trans run_runtime_steps_from_def;

Definition run_runtime_steps_def:
  run_runtime_steps fuel code calldata = run_runtime_steps_from fuel 0 code calldata
End

val () = cv_auto_trans run_runtime_steps_def;

Definition direct_return_uint_runtime_code_def:
  direct_return_uint_runtime_code =
    SND ^(evalCompilerBytecodeLib.read_hex_bytes "direct_return_uint.hex")
End

val () = cv_trans_deep_embedding EVAL direct_return_uint_runtime_code_def;

Theorem direct_return_uint_runtime_call:
  run_runtime_steps 16 direct_return_uint_runtime_code [] =
    SOME (NONE, word_to_bytes_be (1w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Definition direct_return_arg_runtime_code_def:
  direct_return_arg_runtime_code =
    SND ^(evalCompilerBytecodeLib.read_hex_bytes "direct_return_arg.hex")
End

val () = cv_trans_deep_embedding EVAL direct_return_arg_runtime_code_def;

Theorem direct_return_arg_runtime_code_bytes:
  direct_return_arg_runtime_code =
    [0x5Fw; 0x35w; 0x5Fw; 0x52w; 0x36w; 0x5Fw; 0xF3w]
Proof
  CONV_TAC cv_eval
QED

Theorem direct_return_arg_runtime_parsed:
  parse_code 0 FEMPTY direct_return_arg_runtime_code =
    FEMPTY |+ (0, Push 0 []) |+ (1, CallDataLoad) |+
      (2, Push 0 []) |+ (3, MStore) |+ (4, CallDataSize) |+
      (5, Push 0 []) |+ (6, Return)
Proof
  CONV_TAC cv_eval
QED

Theorem word_of_bytes_be_word_to_bytes_be_256:
  word_of_bytes_be (word_to_bytes_be (w : bytes32)) = w
Proof
  simp[word_to_bytes_be_def, word_of_bytes_be_def,
       word_of_bytes_word_to_bytes]
QED

Theorem LENGTH_word_to_bytes_be_256:
  LENGTH (word_to_bytes_be (w : bytes32)) = 32
Proof
  simp[word_to_bytes_be_def, LENGTH_word_to_bytes]
QED

Theorem word_to_bytes_be_reverse_le:
  ∀v:'a word. word_to_bytes v T = REVERSE (word_to_bytes v F)
Proof
  simp[GSYM word_to_bytes_be_def, GSYM word_to_bytes_le_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num,
       cv_stdTheory.word_to_bytes_le_eq_bytes_of_num]
QED

Theorem call_data_load_word_to_bytes_be:
  word_of_bytes F 0w
    (REVERSE (take_pad_0 32 (word_to_bytes_be (w : bytes32)))) = w
Proof
  `LENGTH (REVERSE (word_to_bytes (w : bytes32) F)) = 32` by
    simp[LENGTH_word_to_bytes] >>
  simp[take_pad_0_def, word_to_bytes_be_def, LENGTH_word_to_bytes,
       word_to_bytes_be_reverse_le, TAKE_LENGTH_TOO_LONG, PAD_RIGHT,
       word_of_bytes_word_to_bytes]
QED

Theorem mstore_word_to_bytes_be:
  REVERSE (word_to_bytes (w : bytes32) F) = word_to_bytes_be w
Proof
  simp[word_to_bytes_be_def, word_to_bytes_be_reverse_le]
QED

val direct_return_arg_step_defs = [
  step_def, handle_def, bind_def, return_def, fail_def, assert_def,
  get_current_context_def, set_current_context_def, get_call_data_def,
  runtime_state_with_def, runtime_context_with_def, runtime_context_at_def,
  runtime_context_def, runtime_msg_params_def, direct_return_arg_runtime_parsed,
  direct_return_arg_runtime_code_bytes, empty_return_destination_def,
  FLOOKUP_UPDATE, step_inst_def,
  step_push_def, step_call_data_load_def, step_mstore_def, step_msgParams_def,
  step_context_def, step_return_def, consume_gas_def, push_stack_def,
  pop_stack_def, memory_expansion_info_def, memory_expansion_cost_def,
  memory_cost_def, memory_cost_per_word_def, word_size_def, expand_memory_def,
  write_memory_def, read_memory_def, set_return_data_def, finish_def, handle_step_def,
  handle_create_def, handle_exception_def, get_return_data_def,
  get_output_to_def, get_num_contexts_def, reraise_def, vfm_abort_def,
  inc_pc_or_jump_def,
  ignore_bind_def, is_call_def, LET_THM, opcode_def, word_of_bytes_def,
  mstore_word_to_bytes_be, call_data_load_word_to_bytes_be,
  LENGTH_word_to_bytes_be_256, LENGTH_word_to_bytes, TAKE_LENGTH_TOO_LONG
];

Theorem direct_return_arg_step_push0_offset:
  step (runtime_state_with 0 [] [] [] 0 direct_return_arg_runtime_code
          (word_to_bytes_be (w : bytes32))) =
    (INL (),
     runtime_state_with 1 [0w] [] [] 2 direct_return_arg_runtime_code
       (word_to_bytes_be w))
Proof
  simp direct_return_arg_step_defs
QED

Theorem direct_return_arg_step_calldataload:
  step (runtime_state_with 1 [0w] [] [] 2 direct_return_arg_runtime_code
          (word_to_bytes_be (w : bytes32))) =
    (INL (),
     runtime_state_with 2 [w] [] [] 5 direct_return_arg_runtime_code
       (word_to_bytes_be w))
Proof
  simp direct_return_arg_step_defs
QED

Theorem direct_return_arg_step_push0_mstore_offset:
  step (runtime_state_with 2 [w] [] [] 5 direct_return_arg_runtime_code
          (word_to_bytes_be (w : bytes32))) =
    (INL (),
     runtime_state_with 3 [0w; w] [] [] 7 direct_return_arg_runtime_code
       (word_to_bytes_be w))
Proof
  simp direct_return_arg_step_defs
QED

Theorem direct_return_arg_step_mstore:
  step (runtime_state_with 3 [0w; w] [] [] 7 direct_return_arg_runtime_code
          (word_to_bytes_be (w : bytes32))) =
    (INL (),
     runtime_state_with 4 [] (word_to_bytes_be w) [] 13
       direct_return_arg_runtime_code (word_to_bytes_be w))
Proof
  simp direct_return_arg_step_defs
QED

Theorem direct_return_arg_step_calldatasize:
  step (runtime_state_with 4 [] (word_to_bytes_be w) [] 13
          direct_return_arg_runtime_code (word_to_bytes_be (w : bytes32))) =
    (INL (),
     runtime_state_with 5 [32w] (word_to_bytes_be w) [] 15
       direct_return_arg_runtime_code (word_to_bytes_be w))
Proof
  simp direct_return_arg_step_defs
QED

Theorem direct_return_arg_step_push0_return_offset:
  step (runtime_state_with 5 [32w] (word_to_bytes_be w) [] 15
          direct_return_arg_runtime_code (word_to_bytes_be (w : bytes32))) =
    (INL (),
     runtime_state_with 6 [0w; 32w] (word_to_bytes_be w) [] 17
       direct_return_arg_runtime_code (word_to_bytes_be w))
Proof
  simp direct_return_arg_step_defs
QED

Theorem direct_return_arg_step_return:
  step (runtime_state_with 6 [0w; 32w] (word_to_bytes_be w) [] 17
          direct_return_arg_runtime_code (word_to_bytes_be (w : bytes32))) =
    (INR NONE,
     runtime_state_with 6 [] (word_to_bytes_be w) (word_to_bytes_be w) 17
       direct_return_arg_runtime_code (word_to_bytes_be w))
Proof
  simp direct_return_arg_step_defs
QED

Theorem direct_return_arg_run_steps:
  run_steps 16
    (runtime_state_with 0 [] [] [] 0 direct_return_arg_runtime_code
       (word_to_bytes_be (w : bytes32))) =
    SOME (NONE,
      runtime_state_with 6 [] (word_to_bytes_be w) (word_to_bytes_be w) 17
        direct_return_arg_runtime_code (word_to_bytes_be w))
Proof
  simp[run_steps_compute_thm,
       direct_return_arg_step_push0_offset,
       direct_return_arg_step_calldataload,
       direct_return_arg_step_push0_mstore_offset,
       direct_return_arg_step_mstore,
       direct_return_arg_step_calldatasize,
       direct_return_arg_step_push0_return_offset,
       direct_return_arg_step_return]
QED

Theorem direct_return_arg_runtime_call:
  ∀w.
    run_runtime_steps 16 direct_return_arg_runtime_code
      (word_to_bytes_be (w : bytes32)) =
      SOME (NONE, word_to_bytes_be w)
Proof
  simp[run_runtime_steps_def, run_runtime_steps_from_def,
       runtime_state_at_0] >>
  simp[direct_return_arg_run_steps] >>
  simp[runtime_state_with_def, runtime_context_with_def]
QED

Definition return_arg_source_program_def:
  return_arg_source_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Name (BaseT (UintT 256)) "x"))]]
End

Definition return_arg_source_machine_def:
  return_arg_source_machine =
    initial_machine_state with
      sources := [(0w, [(NONE, return_arg_source_program)])]
End

Definition return_arg_source_tx_def:
  return_arg_source_tx (w : bytes32) =
    empty_call_txn with
      <| target := 0w;
         function_name := "foo";
         args := [vyperValue$IntV (&w2n w)] |>
End

Definition return_arg_source_return_data_def:
  return_arg_source_return_data (w : bytes32) =
    case call_external return_arg_source_machine (return_arg_source_tx w) of
    | (INL v, _) =>
        (case vyper_to_abi (type_env return_arg_source_program)
                (BaseT (UintT 256)) v of
         | NONE => NONE
         | SOME abi_v => SOME (enc (Uint 256) abi_v))
    | (INR _, _) => NONE
End

Definition runtime_success_return_data_def:
  runtime_success_return_data res =
    case res of
    | SOME (NONE, bs) => SOME bs
    | _ => NONE
End

Theorem within_int_bound_uint256_w2n:
  within_int_bound (Unsigned 256) (&w2n (w : bytes32))
Proof
  simp[within_int_bound_def, integerTheory.NUM_OF_INT] >>
  PURE_REWRITE_TAC[GSYM (EVAL ``dimword (:256)``)] >>
  simp[wordsTheory.w2n_lt]
QED

Theorem enc_uint256_w2n:
  enc (Uint 256) (NumV (w2n (w : bytes32))) = word_to_bytes_be w
Proof
  simp[enc_def, enc_number_def, word_to_bytes_be_def]
QED

Theorem return_arg_source_call:
  call_external return_arg_source_machine (return_arg_source_tx w) =
    (INL (vyperValue$IntV (&w2n (w : bytes32))),
     return_arg_source_machine)
Proof
  simp[return_arg_source_program_def,
       return_arg_source_machine_def, return_arg_source_tx_def,
       vyperContextTheory.empty_call_txn_def,
       vyperInterpreterTheory.call_external_def,
       vyperInterpreterTheory.find_function_module_def,
       vyperInterpreterTheory.lookup_exported_function_def,
       vyperInterpreterTheory.call_external_function_def,
       vyperInterpreterTheory.lookup_function_def,
       vyperInterpreterTheory.initial_machine_state_def,
       vyperInterpreterTheory.lookup_nonreentrant_slot_def,
       vyperInterpreterTheory.bind_arguments_def,
       vyperInterpreterTheory.evaluate_defaults_def,
       vyperInterpreterTheory.send_call_value_def,
       vyperInterpreterTheory.initial_evaluation_context_def,
       vyperInterpreterTheory.abstract_machine_from_state_def,
       vyperValueTheory.evaluate_type_def,
       vyperValueOperationTheory.safe_cast_def,
       within_int_bound_uint256_w2n,
       vyperInterpreterTheory.initial_state_def,
       vyperInterpreterTheory.evaluate_def,
       vyperStateTheory.get_scopes_def,
       vyperStateTheory.lookup_scopes_val_def,
       vyperStateTheory.materialise_def,
       vyperStateTheory.lift_option_type_def,
       vyperStateTheory.return_def,
       vyperStateTheory.raise_def,
       vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def,
       vyperContextTheory.get_self_code_def,
       vyperContextTheory.get_module_code_def,
       vyperContextTheory.type_env_all_modules_def,
       FLOOKUP_UPDATE]
QED

Theorem return_arg_source_return_data_bytes:
  return_arg_source_return_data (w : bytes32) = SOME (word_to_bytes_be w)
Proof
  simp[return_arg_source_return_data_def, return_arg_source_call,
       enc_uint256_w2n, integerTheory.NUM_OF_INT]
QED

Theorem direct_return_arg_source_runtime_equiv:
  ∀w.
    return_arg_source_return_data w =
      runtime_success_return_data
        (run_runtime_steps 16 direct_return_arg_runtime_code
          (word_to_bytes_be (w : bytes32)))
Proof
  simp[return_arg_source_return_data_bytes,
       direct_return_arg_runtime_call, runtime_success_return_data_def]
QED
