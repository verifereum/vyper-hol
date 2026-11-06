(* Whitelist removal, S1 leaf: the runtime-unit simulation theorem without
   supported_program.  Admitted here so vyper_call_correct can drop the
   premise; proved piece by piece, one leaf per excluded form, and wired
   into body_sim_mutual when the supported_* clauses widen. *)
Theory whitelistS1
Ancestors
  loweringRuntimeCorrect

(* lower_vyper_runtime_unit_correct without supported_program: the type
   checker (source_typing_ok) is the only restriction on the program. *)
Theorem lower_vyper_runtime_unit_correct_full:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes
    ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  cheat
QED
