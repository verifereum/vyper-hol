(* Execute the independent pinned runtime bytes through the EVM model.
   Compiler parity is proved separately; these tests specify the observable
   behavior that the source and emitted entries must share. *)
Theory vyperExternalEntryBehavior
Ancestors
  vyperInterpreter vyperContext vyperState vfmExecution vfmState
Libs
  evalCompilerBytecodeLib cv_transLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../lowering/defs/bytecode/external-entries"]
fun entry_runtime name = snd (pairSyntax.dest_pair
  (evalCompilerBytecodeLib.read_hex_bytes
    ("../external-entries/oracle/" ^ name ^ ".hex")))

Definition entry_behavior_accounts_def:
  entry_behavior_accounts code =
    update_account 42w (empty_account_state with balance := 100)
      (update_account 43w (empty_account_state with code := code) empty_accounts)
End
val () = cv_auto_trans entry_behavior_accounts_def;

Definition entry_behavior_observe_def:
  entry_behavior_observe code calldata amount =
    case run_ext_call 42w 43w calldata (SOME amount) default_evm_gas_limit
      (entry_behavior_accounts code) empty_transient_storage
      (vyper_to_tx_params empty_call_txn) of
      NONE => NONE
    | SOME (ok,bytes,accounts,transient,logs) =>
        SOME (ok,(word_of_bytes_be bytes : bytes32),
          lookup_storage 0w (lookup_account 43w accounts).storage,
          lookup_storage 0w (lookup_transient_storage 43w transient))
End
val () = cv_auto_trans entry_behavior_observe_def;

Definition nr_behavior_code_def:
  nr_behavior_code = ^(entry_runtime "nr_ext_nonpayable")
End
val () = cv_auto_trans nr_behavior_code_def;

Definition defaults_multi_behavior_code_def:
  defaults_multi_behavior_code = ^(entry_runtime "dflt_multi")
End
val () = cv_auto_trans defaults_multi_behavior_code_def;

Definition defaults_sender_behavior_code_def:
  defaults_sender_behavior_code = ^(entry_runtime "dflt_sender")
End
val () = cv_auto_trans defaults_sender_behavior_code_def;

Definition defaults_balance_behavior_code_def:
  defaults_balance_behavior_code = ^(entry_runtime "dflt_balance_after_transfer")
End
val () = cv_auto_trans defaults_balance_behavior_code_def;

Definition defaults_effect_behavior_code_def:
  defaults_effect_behavior_code = ^(entry_runtime "dflt_effectful_constant_index")
End
val () = cv_auto_trans defaults_effect_behavior_code_def;

Definition nr_internal_return_behavior_code_def:
  nr_internal_return_behavior_code = ^(entry_runtime "nr_internal_return")
End
val () = cv_auto_trans nr_internal_return_behavior_code_def;

Definition nr_internal_early_behavior_code_def:
  nr_internal_early_behavior_code = ^(entry_runtime "nr_internal_early_return")
End
val () = cv_auto_trans nr_internal_early_behavior_code_def;

Theorem nonreentrant_preserves_storage_slot_zero:
  entry_behavior_observe nr_behavior_code
    ([179w;222w;100w;139w] ++ REPLICATE 31 0w ++ [5w]) 0 =
      SOME (T,6w,5w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem defaults_short_prefix_behavior:
  entry_behavior_observe defaults_multi_behavior_code
    ([179w;222w;100w;139w] ++ REPLICATE 31 0w ++ [5w]) 0 =
      SOME (T,5w,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem defaults_partial_prefix_behavior:
  entry_behavior_observe defaults_multi_behavior_code
    ([39w;53w;172w;183w] ++ REPLICATE 31 0w ++ [5w] ++
      REPLICATE 31 0w ++ [1w]) 0 = SOME (T,5w,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem defaults_full_prefix_behavior:
  entry_behavior_observe defaults_multi_behavior_code
    ([135w;148w;116w;219w] ++ REPLICATE 31 0w ++ [5w] ++
      REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w) 0 =
      SOME (T,5w,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem defaults_sender_behavior:
  entry_behavior_observe defaults_sender_behavior_code
    [38w;18w;31w;240w] 0 = SOME (T,42w,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem defaults_observe_balance_after_transfer:
  entry_behavior_observe defaults_balance_behavior_code
    [38w;18w;31w;240w] 7 = SOME (T,93w,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem defaults_retain_internal_storage_effect:
  entry_behavior_observe defaults_effect_behavior_code
    [38w;18w;31w;240w] 0 = SOME (T,21w,1w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem internal_value_return_releases_lock:
  entry_behavior_observe nr_internal_return_behavior_code
    ([179w;222w;100w;139w] ++ REPLICATE 31 0w ++ [5w]) 0 =
      SOME (T,10w,5w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem internal_early_return_releases_lock:
  entry_behavior_observe nr_internal_early_behavior_code
    ([179w;222w;100w;139w] ++ REPLICATE 31 0w ++ [5w]) 0 =
      SOME (T,0w,0w,0w)
Proof
  CONV_TAC cv_eval
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("entry behavior has oracle dependencies: " ^ name)
  end) (DB.thms "vyperExternalEntryBehavior");
