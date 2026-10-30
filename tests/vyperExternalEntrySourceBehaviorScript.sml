(* Run the same witnesses through source deployment and external calls.
   Importing the EVM behavior theory checks both sides of the examples. *)
Theory vyperExternalEntrySourceBehavior
Ancestors
  vyperExternalEntryBehavior vyperInterpreter vyperContext vyperState
  vyperSmallStep[ignore_grammar] vyperValue vfmExecution vfmState
Libs
  proofAuditLib
  vyperCheckContractFrontendLib vyperCheckContractLib jsonASTLib JSONDecode
  cv_transLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../lowering/defs/bytecode/external-entries"]
fun entry_source_fixture name = let
  val path = "../lowering/defs/bytecode/external-entries/ast/" ^ name ^ ".json"
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = ``43w : address``,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  val checked = vyperCheckContractLib.check_contract input
  val _ = optionSyntax.dest_some (rhs (concl checked))
in pairSyntax.mk_pair (#modules input,#layouts input) end

Definition entry_source_observe_def:
  entry_source_observe (modules,layouts) code vals amount =
    let am = initial_machine_state with
      <| accounts := entry_behavior_accounts code; layouts := layouts |> in
    let deploy_tx = empty_call_txn with
      <| sender := 42w; target := 43w; function_name := "__init__" |> in
    case load_contract NONE am deploy_tx modules [] of
      INR e => NONE
    | INL (deployed,_) =>
        let tx = deploy_tx with
          <| function_name := "f"; args := vals; value := amount |> in
        let (result,called,_) = call_external_transaction NONE deployed tx in
        case result of
          INR e => NONE
        | INL v => SOME (v,
            lookup_storage 0w (lookup_account 43w called.accounts).storage,
            lookup_storage 0w (lookup_transient_storage 43w called.tStorage))
End
val () = cv_auto_trans entry_source_observe_def;

Definition nr_source_input_def:
  nr_source_input = ^(entry_source_fixture "nr_ext_nonpayable")
End
val () = cv_auto_trans nr_source_input_def;

Definition defaults_multi_source_input_def:
  defaults_multi_source_input = ^(entry_source_fixture "dflt_multi")
End
val () = cv_auto_trans defaults_multi_source_input_def;

Definition defaults_sender_source_input_def:
  defaults_sender_source_input = ^(entry_source_fixture "dflt_sender")
End
val () = cv_auto_trans defaults_sender_source_input_def;

Definition defaults_balance_source_input_def:
  defaults_balance_source_input = ^(entry_source_fixture "dflt_balance_after_transfer")
End
val () = cv_auto_trans defaults_balance_source_input_def;

Definition defaults_effect_source_input_def:
  defaults_effect_source_input = ^(entry_source_fixture "dflt_effectful_constant_index")
End
val () = cv_auto_trans defaults_effect_source_input_def;

Definition nr_internal_return_source_input_def:
  nr_internal_return_source_input = ^(entry_source_fixture "nr_internal_return")
End
val () = cv_auto_trans nr_internal_return_source_input_def;

Definition nr_internal_early_source_input_def:
  nr_internal_early_source_input = ^(entry_source_fixture "nr_internal_early_return")
End
val () = cv_auto_trans nr_internal_early_source_input_def;

Theorem source_nonreentrant_preserves_storage_slot_zero:
  entry_source_observe nr_source_input nr_behavior_code [IntV 5] 0 =
    SOME (IntV 6,5w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem source_defaults_short_prefix_behavior:
  entry_source_observe defaults_multi_source_input defaults_multi_behavior_code
    [IntV 5] 0 = SOME (IntV 5,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem source_defaults_partial_prefix_behavior:
  entry_source_observe defaults_multi_source_input defaults_multi_behavior_code
    [IntV 5;BoolV T] 0 = SOME (IntV 5,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem source_defaults_full_prefix_behavior:
  entry_source_observe defaults_multi_source_input defaults_multi_behavior_code
    [IntV 5;BoolV T;BytesV (REPLICATE 20 0w)] 0 = SOME (IntV 5,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem source_defaults_sender_behavior:
  entry_source_observe defaults_sender_source_input defaults_sender_behavior_code
    [] 0 = SOME (BytesV (REPLICATE 19 0w ++ [42w]),0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem source_defaults_observe_balance_after_transfer:
  entry_source_observe defaults_balance_source_input defaults_balance_behavior_code
    [] 7 = SOME (IntV 93,0w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem source_defaults_retain_internal_storage_effect:
  entry_source_observe defaults_effect_source_input defaults_effect_behavior_code
    [] 0 = SOME (IntV 21,1w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem source_internal_value_return_releases_lock:
  entry_source_observe nr_internal_return_source_input nr_internal_return_behavior_code
    [IntV 5] 0 = SOME (IntV 10,5w,0w)
Proof
  CONV_TAC cv_eval
QED

Theorem source_internal_early_return_releases_lock:
  entry_source_observe nr_internal_early_source_input nr_internal_early_behavior_code
    [IntV 5] 0 = SOME (NoneV,0w,0w)
Proof
  CONV_TAC cv_eval
QED

val () = proofAuditLib.check_theory "vyperExternalEntrySourceBehavior";
