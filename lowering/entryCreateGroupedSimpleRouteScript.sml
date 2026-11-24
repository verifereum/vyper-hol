(* The selected singleton and fallback routes stop either at the registered
   body endpoint or at the concrete grouped value rejection. *)
Theory entryCreateGroupedSimpleRoute
Ancestors
  groupedValueRejectSite groupedLegacyCallRoute groupedFallbackCallRoute
  compileVyper entryStateRel e2eDefs gasShadowUnit venomState vyperCalldata
  vyperInterpreter vyperCall runtimeEntryEndpoint list words

Theorem grouped_singleton_selected_route_cases:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts =
    cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
      SOME (tx.function_name,tys) /\
  OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
  calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = SOME tx.args /\
  (grouped_value_reject_site unit vs ==> Q) ==>
  (?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args [] ret
    (subst_consts_stmts (module_consts_env tops []) fbody)) \/ Q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac grouped_legacy_call_route_with_reject_site >>
  metis_tac[]
QED

Theorem grouped_fallback_selected_route_cases:
  lower_vyper_runtime_unit tops rp = SOME unit /\ supported_program tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name,tx.args) /\
  (LENGTH vs.vs_call_ctx.cc_calldata < 4 \/
   FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector vs.vs_call_ctx.cc_calldata)
     (abi_external_signatures tops) = NONE) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,ds,ret,fbody) /\
  (grouped_value_reject_site unit vs ==> Q) ==>
  (?es. runtime_body_endpoint tops rp unit am tx vs es mut nr args ds ret
    (subst_consts_stmts (module_consts_env tops []) fbody)) \/ Q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac grouped_fallback_call_route_with_reject_site >>
  metis_tac[]
QED
