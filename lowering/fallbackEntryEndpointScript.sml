(*
 * The runtime entry for calldata dispatching to __default__ (fewer than 4
 * bytes, or a selector matching no signature) reaches the body's endpoint
 * (runtimeEntryEndpoint) at the fallback: the Linear dispatch falls
 * through every selector check to the fallback label, whose payable check
 * is compile_entry_checks at minimum calldata size 4.
 *
 * TOP-LEVEL:
 *   dispatched_entry_endpoint_default
 *)
Theory fallbackEntryEndpoint
Ancestors
  runtimeEntryEndpoint vyperCalldata

Theorem dispatched_entry_endpoint_default:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    tx.function_name = "__default__" /\
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
