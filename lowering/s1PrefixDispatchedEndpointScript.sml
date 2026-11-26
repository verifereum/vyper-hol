(* Actual runtime dispatch either reaches the bound body or has no outcome. *)
Theory s1PrefixDispatchedEndpoint
Ancestors
  s1PrefixPlainDispatch s1PrefixOutcomeFreeEntry loweringCalldataCorrect
  groupedDefaultCallRoute groupedFallbackCallRoute groupedLegacyCallRoute
  defaultDispatchFacts runtimePeakMemoryBound
  lowerDloadDefs exprSimHypsDefs vyperLoweringCorrect

val _ = Parse.hide "tops";

fun finish_grouped_route_tac defaults th =
  drule_all th >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `es0` assume_tac)
    (qx_choose_then `marks` (map_every assume_tac o CONJUNCTS)))
  >- (disj2_tac >> qexistsl_tac [`mut`,`nr`,`args`,defaults,`fbody`,`es0`] >>
      asm_rewrite_tac[]) >>
  disj1_tac >> irule outcome_free_entry_prefix_cert >> asm_rewrite_tac[] >>
  qexistsl_tac [`marks`,`ret`] >> asm_rewrite_tac[];

Theorem dispatched_prefix_endpoint_cases:
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
  unit_prefix_cert shadow_unit.cu_context tops am tx unit vs \/
  ?mut nr args dflts fbody es0.
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args dflts ret
      (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `outcomes_accounts_typed (SOME vs.vs_outcomes)` by simp[outcomes_accounts_typed_def] >>
  `(ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254)` by decide_tac >>
  `(ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s)` by
    (strip_tac >> rpt gen_tac >> strip_tac >>
     irule lower_vyper_runtime_unit_raw_headroom >>
     qpat_assum `raw_reachable _ _ _ _ _` (irule_at Any) >>
     qpat_assum `lower_vyper_runtime_unit _ _ = _` (irule_at Any) >>
     qpat_assum `initial_venom_state_rel _ _ _ _` (irule_at Any) >> asm_rewrite_tac[]) >>
  qpat_x_assum `dispatched_vyper_call _ _ _ _`
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`mut`,`nr`,`args`,`dflts`,`fbody`] assume_tac) o
     REWRITE_RULE [dispatched_vyper_call_def]) >>
  reverse (Cases_on `EXISTS external_has_defaults (FST (classify_functions tops))`)
  >- drule_all_then ACCEPT_TAC plain_dispatched_prefix_endpoint_cases >>
  `~vs.vs_halted` by fs[initial_venom_state_rel_def] >>
  drule default_dispatch_raw_cases >>
  disch_then (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS) strip_assume_tac)
  >- finish_grouped_route_tac `dflts` grouped_fallback_call_route >>
  Cases_on `dflts = []`
  >- (qpat_x_assum `dflts = []` SUBST_ALL_TAC >>
      finish_grouped_route_tac `[]` grouped_legacy_call_route) >>
  finish_grouped_route_tac `dflts` grouped_default_call_route
QED
