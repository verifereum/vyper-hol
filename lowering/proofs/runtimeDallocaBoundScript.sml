(* Source-call bounds supply the reachable dynamic-allocation frontier. *)
Theory runtimeDallocaBound
Ancestors
  compileVyper vyperCompiler vyperLoweringCorrect e2eDefs sourceCallCount
  exprSimHypsDefs lowerDloadDefs contextRawReachable venomLayout

val _ = Parse.hide "tops";

Theorem lower_vyper_runtime_unit_dalloca_bound:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (!obs. source_calls_within (2 ** 64) am tx vs.vs_outcomes obs) /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) ==>
    !f i s.
       raw_reachable vs unit.cu_context f i s ==>
       s.vs_initial_fmp = vs.vs_initial_fmp /\
       w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
       (i.inst_opcode = DALLOCA ==>
        !sz_op sz.
          i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
          w2n s.vs_fmp + ceil32 (w2n sz) < dimword (:256))
Proof
  cheat
QED
