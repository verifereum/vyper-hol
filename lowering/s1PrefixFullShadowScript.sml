(* The full execution certificate at the shadow chosen by runtime lowering. *)
Theory s1PrefixFullShadow
Ancestors
  loweringCalldataCorrect sourceUnitExecution gasShadowRunLowering
  e2eDefs vyperLoweringCorrect supportedProgram exprSimHypsDefs
  extCallOracle lowerDloadDefs venomCompilerTypes venomState words list

Theorem dispatched_full_at_runtime_shadow:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
  initial_venom_state_rel tops am tx vs /\
  code_layout_valid vs /\
  EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
               accounts_runtime_well_typed oc.co_accounts) vs.vs_outcomes /\
  LENGTH vs.vs_outcomes < 2 ** 64 /\
  vs.vs_fmp = vs.vs_initial_fmp /\
  w2n vs.vs_initial_fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp ==>
  ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
            tops ret am tx unit vs
Proof
  strip_tac >>
  drule_all lower_vyper_runtime_unit_correct_dispatched_with_shadow >>
  disch_then (qx_choose_then `su` strip_assume_tac) >>
  `su = shadow_unit` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `su = shadow_unit` SUBST_ALL_TAC >>
  first_x_assum (qspecl_then [`am`, `tx`, `ret`, `vs`] mp_tac) >>
  simp[outcomes_accounts_typed_def]
QED
