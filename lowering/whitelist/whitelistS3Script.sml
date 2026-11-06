(* Whitelist removal, S3 leaves: the memory-safety facts of the lowered
   unit without supported_program.  Same statements as loweringMemCorrect's,
   minus supported_program and minus the no-DALLOCA premise: the whitelist
   admits forms the lowering compiles with DALLOCA (create, raw_call of
   msg.data), so the O1 shape stops excluding it (#963) and memory safety
   must cover it. *)
Theory whitelistS3
Ancestors
  loweringMemCorrect

Theorem lower_vyper_runtime_unit_memory_ok_full:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx))
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within
          (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
          unit.cu_context vs
Proof
  cheat
QED

Theorem lower_vyper_runtime_unit_dload_offset_ok_full:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    code_layout_valid vs /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx)
    ==> mem_inv dload_offset_ok unit.cu_context vs
Proof
  cheat
QED
