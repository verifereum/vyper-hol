Theory evalCompilerRuntime
Ancestors
  byte finite_map finite_set list option pair words
  vfmContext vfmExecution vfmState vfmTransaction vfmCompute[ignore_grammar]
Libs
  cv_transLib evalCompilerBytecodeLib finite_mapLib wordsLib

(* TOP-LEVEL:
 *   run_runtime_steps       -- execute bytecode in a minimal single-frame state
 *   run_runtime_steps_from  -- same, with an explicit initial program counter
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

Definition run_steps_def:
  run_steps 0 s = NONE ∧
  run_steps (SUC fuel) s =
    case step s of
      (INL _, s') => run_steps fuel s'
    | (INR result, s') => SOME (result, s')
End

val () = cv_auto_trans run_steps_def;

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
