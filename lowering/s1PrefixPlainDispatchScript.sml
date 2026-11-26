(* Plain runtime dispatch: value rejection or the selected post-binding endpoint. *)
Theory s1PrefixPlainDispatch
Ancestors
  s1PrefixOutcomeFreeEntry s1PrefixRegisteredEndpoint
  loweringCalldataCorrect[qualified,ignore_grammar]
  dispatchedArgsBind dispatchedValueSource dispatchedEntryValueRevert
  dispatchedSelectedEndpoint fallbackEntryEndpoint loweringRuntimeCorrect
  gasShadowRunLowering gasShadowUnit gasSummary vyperLoweringCorrect
  runtimeEntryEndpoint compileVyper constSubst vyperCalldata
  vyperCall vyperContext vyperState venomState words

Theorem plain_dispatched_prefix_endpoint_cases:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  supported_program tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  (ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s) /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name,tx.args) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  unit_prefix_cert shadow_unit.cu_context tops am tx unit vs \/
  ?mut nr args dflts fbody es0.
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args dflts ret
      (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then SUBST_ALL_TAC
    loweringCalldataCorrectTheory.selected_legacy_defaults_nil >>
  drule_all dispatched_vyper_call_bind >>
  disch_then (qx_choose_then `env` assume_tac) >>
  namedCases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>)`
    ["res es0"] >>
  namedCases_on `res` ["u", "exc"]
  >- (Cases_on `u` >> disj2_tac >>
      qexistsl_tac [`mut`,`nr`,`args`,`[]`,`fbody`,`es0`] >>
      asm_rewrite_tac[] >> Cases_on `nr`
      >- (drule_all_then ACCEPT_TAC dispatched_nonreentrant_endpoint) >>
      irule runtime_entry_endpoint_body_endpoint >>
      asm_rewrite_tac[] >> conj_tac
      >- (qexists_tac `env` >> asm_rewrite_tac[]) >>
      Cases_on `tx.function_name = "__default__"`
      >- drule_all_then ACCEPT_TAC dispatched_entry_endpoint_default >>
      drule_all_then ACCEPT_TAC dispatched_entry_endpoint_selected) >>
  disj1_tac >>
  `~vs.vs_halted /\ value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
  drule_all source_dispatched_value_reject_trace_nr >> strip_tac >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     drule_all runtime_gas_shadow_unit_exists >> simp[gas_shadow_unit_def]) >>
  drule_all external_entry_value_revert_dispatched_with_nr >> strip_tac >>
  irule outcome_free_entry_prefix_cert >> asm_rewrite_tac[] >>
  qexistsl_tac [`[]`,`ret`] >> simp[gas_explicit_def]
QED
