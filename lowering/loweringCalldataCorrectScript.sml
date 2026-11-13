(* S1 and S3 for every calldata: the call the calldata dispatches to
   (dispatched_vyper_call, including __default__ and noncanonical
   encodings), and the calldata that dispatches to nothing, which reverts
   with no data. *)
Theory loweringCalldataCorrect
Ancestors
  vyperCalldata calldataExact e2eDefs vyperLoweringCorrect loweringRuntimeCorrect
  loweringMemCorrect

(* The call a contract makes of raw calldata: the external entry it
   dispatches to and the arguments it decodes (vyperCalldata), including the
   __default__ fallback and noncanonical encodings.  Nonreentrant functions
   and functions with default arguments stay excluded for now. *)
Definition dispatched_vyper_call_def:
  dispatched_vyper_call tops tx calldata ret <=>
    calldata_dispatch tops calldata = SOME (tx.function_name, tx.args) /\
    ?mut args body.
      vyperInterpreter$lookup_function NONE tx.function_name External tops =
        SOME (mut, F, args, [], ret, body)
End

(* S1 *)
Theorem lower_vyper_runtime_unit_correct_dispatched:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes
    ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  (* HELD ADMISSION SEQ-4939: S1 for noncanonical/__default__ dispatch; needs the entry chain over calldata_exact_owned_run *)
  cheat
QED

(* S1, calldata that dispatches to nothing: no fallback, a short head, or a
   failed decode.  The entry reverts with empty returndata before any
   function body runs. *)
Theorem lower_vyper_runtime_unit_reverts:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs
    ==>
    ?fuel s. run_context fuel unit.cu_context vs = Abort Revert_abort s /\
             s.vs_returndata = []
Proof
  (* HELD ADMISSION SEQ-4940: S1 revert on a NONE dispatch; needs the selector-miss and decode-failure entry runs *)
  cheat
QED

(* S3 *)
Theorem lower_vyper_runtime_unit_memory_ok_dispatched:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    ~ctx_has_dalloca unit.cu_context
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within
          (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
          unit.cu_context vs
Proof
  (* HELD ADMISSION SEQ-4941: S3 twin of SEQ-4939 *)
  cheat
QED

(* S3, calldata that dispatches to nothing. *)
Theorem lower_vyper_runtime_unit_reverts_memory_ok:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        ?D. dead_wf D /\ taint_within D unit.cu_context vs
Proof
  (* HELD ADMISSION SEQ-4942: S3 twin of SEQ-4940 *)
  cheat
QED

(* DLOAD offsets stay within the data section, for every dispatched call. *)
Theorem lower_vyper_runtime_unit_dload_offset_ok_dispatched:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    code_layout_valid vs /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx))
    ==> mem_inv dload_offset_ok unit.cu_context vs
Proof
  (* HELD ADMISSION SEQ-4943: dispatched form of the proved canonical dload_offset_ok *)
  cheat
QED
