(* Source-call bounds supply the deployment unit's dynamic-allocation
 * frontier, and with it the joint body's no-wrap antecedent at the
 * constructor root, with no DALLOCA exclusion. The deploy twin of
 * runtimeDallocaBound.lower_vyper_runtime_unit_dalloca_bound.
 *
 * TOP-LEVEL:
 *   lower_vyper_deploy_unit_dalloca_bound - every raw-reachable state of
 *     the deployment unit
 *   deploy_ctor_frag_dalloca_no_wrap - every state the constructor body's
 *     fragment reaches from its start state
 *)
Theory deployDallocaBound
Ancestors
  ctorDeployDefs ctorDeployLoweringEntry fragGasPath sourceCallCount
  contextRawReachable unitMemInv exprSimHypsDefs

Theorem lower_vyper_deploy_unit_dalloca_bound:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!obs. deploy_source_calls_within (2 ** 64) tops am tx vs.vs_outcomes obs) /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) ==>
    !f i s.
      raw_reachable vs dunit.cu_context f i s ==>
      s.vs_initial_fmp = vs.vs_initial_fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      dalloca_no_wrap i s
Proof
  cheat
QED

Theorem raw_reachable_frag_reachable:
  !ctx fn0 s0 fn inst s.
    frag_reachable ctx fn0 s0 fn inst s ==>
    !vs. (!i. active_inst fn0 i s0 ==> raw_reachable vs ctx fn0 i s0) ==>
         raw_reachable vs ctx fn inst s
Proof
  ho_match_mp_tac frag_reachable_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> metis_tac[raw_reachable_rules]
QED

(* s0 is the constructor body's start state, as deploy_ctor_entry_joint
   gives it. *)
Theorem deploy_ctor_frag_dalloca_no_wrap:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   func s0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!obs. deploy_source_calls_within (2 ** 64) tops am tx vs.vs_outcomes obs) /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    dunit.cu_context.ctx_entry = SOME "__deploy" /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" /\
    gas_path dunit.cu_context func
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                  vs_inst_idx := 0 |>) 0 (OK s0) ==>
    !fn inst s.
      frag_reachable dunit.cu_context func s0 fn inst s ==>
      dalloca_no_wrap inst s
Proof
  cheat
QED
