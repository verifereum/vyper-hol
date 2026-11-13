(*
 * The runtime entry for any calldata dispatching to a named external
 * function (vyperCalldata's calldata_dispatch), canonical encoding or not,
 * reaches the body's endpoint (runtimeEntryEndpoint).  The selector check
 * and payable check are externalEntryJoint's; the argument registration
 * runs the decoder on the actual calldata (calldataExact's
 * calldata_exact_owned_run) in place of the canonical encoding.
 *
 * TOP-LEVEL:
 *   dispatched_entry_endpoint_selected
 *)
Theory dispatchedEntryEndpoint
Ancestors
  runtimeEntryEndpoint vyperCalldata calldataExact

Theorem dispatched_entry_endpoint_selected:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    tx.function_name <> "__default__" /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody
Proof
  (* SEQ-4939 leaf (open) *)
  cheat
QED
