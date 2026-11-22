(* A legacy job reached through the grouped selector, not the plain dispatcher. *)
Theory groupedLegacyCallRoute
Ancestors
  groupedRuntimeBodyCode groupedDispatchPath groupedEntryPackage groupedEntryResources
  groupedEntryExit groupedRegisteredBody groupedEntryAllocation
  runtimeEntryEndpoint registrationRejectMetadata entryRejectAllocationIds
  externalBodyFrame externalReturnPackage defaultEntrySourcePreparation packagedRegistrationProps
  dispatchedArgsBind sourceValueRejection selectedAcceptedSingleton selectedAcceptedDecoder
  externalEntryBound gasShadowRuntimeDispatch gasShadowUnit gasShadowState
  vyperCalldata vyperLoweringCorrect e2eDefs compileVyper compileEnv moduleLowering
  ptrDiscipline venomState venomInst list words entryStateRel vyperInterpreter
  sourceUnitExecution gasSummary vyperABI
  groupedLegacyPairedCode groupedLegacyRegistrationMetadata groupedLegacyCheckSeam
  groupedLegacyCheckedRoute groupedLegacyBoundRegistration groupedRuntimeEndpoint groupedDefaultArguments
  fragGasOriginPtr venomExecSemantics selectedAcceptedFold constSubst
  gasShadowRuntimeBodies gasShadowModuleDefs gasShadow
  entryValueRejectFacts loweringStateRelDefs vyperState vyperCall finite_map
  groupedValueRejectSite

Theorem grouped_legacy_call_route_with_reject_site:
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
  calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = SOME tx.args ==>
  (?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args [] ret
    (subst_consts_stmts (module_consts_env tops []) fbody)) \/
  (grouped_value_reject_site unit vs /\
   ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
      tops ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail. FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading"))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  drule_all grouped_selected_legacy_entry_shape >>
  disch_then (qspecl_then [`T`,`rpolicy.rpol_target`,`K global_nonreentrant_slot`]
    (qx_choosel_then [`pre`,`post`,`lbl`,`z`,`pkg`] strip_assume_tac)) >>
  `MEM (tx.function_name,tys) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  drule_all dispatched_selector_args_bind >> strip_tac >>
  drule_all grouped_source_signature >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [constSubstCorrectTheory.subst_consts_exprs_map]) >>
  `MEM (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
     tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)
     (FST (classify_functions tops))` by simp[] >>
  `LENGTH tx.args = LENGTH args` by
    (drule calldata_decode_args_length >>
     qpat_assum `OPT_MMAP _ tys = _` (mp_tac o MATCH_MP vyperTypeABITheory.OPT_MMAP_LENGTH) >>
     simp[]) >>
  qpat_x_assum `tys = MAP SND args` SUBST_ALL_TAC >>
  irule grouped_legacy_checked_route_with_reject_site >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `env` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `tvs` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `calldata_decode_args u.vs_call_ctx.cc_calldata tvs 0 = SOME tx.args` by simp[] >>
      drule_all_then ACCEPT_TAC
        (REWRITE_RULE [] (Q.INST [`cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`]
          (SPEC_ALL grouped_legacy_bound_registration)))) >>
  qexistsl_tac [`lbl`,`pkg`,`post`,`pre`,`z`] >>
  asm_rewrite_tac[]
QED

Theorem grouped_legacy_call_route:
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
  calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = SOME tx.args ==>
  (?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args [] ret
    (subst_consts_stmts (module_consts_env tops []) fbody)) \/
  (?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
      tops ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail. FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading"))))
Proof
  disch_then (mp_tac o MATCH_MP grouped_legacy_call_route_with_reject_site) >>
  strip_tac >> metis_tac[]
QED
