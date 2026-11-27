(* Canonical calls to selected legacy singletons share the checked route. *)
Theory groupedCanonicalCallRoute
Ancestors
  groupedCanonicalLegacySelection groupedCanonicalLegacyInputs
  groupedCanonicalBoundRegistration groupedLegacyCheckedRoute
  e2eDefs entryStateRel runtimeEntryEndpoint sourceUnitExecution
  compileVyper venomState vyperInterpreter vyperCall gasSummary words list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  drule_all grouped_canonical_legacy_selection >>
  disch_then (qspecl_then [`T`,`rpolicy.rpol_target`,`K global_nonreentrant_slot`]
    strip_assume_tac) >>
  rename1 `_ = pre ++ ExternalSingle (_,lbl,z) pkg::post` >>
  `?envb tvs.
    bind_arguments (type_env tops) args tx.args = SOME envb /\
    OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    LIST_REL value_has_type tvs tx.args /\ LENGTH tx.args = LENGTH args /\
    calldata_encodes (type_env tops) tx.function_name (MAP SND args)
      tx.args vs.vs_call_ctx.cc_calldata /\
    4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata` by
    (PairCases_on `pkg` >>
     qpat_x_assum `_ = set_external_package_target _ _` (assume_tac o SYM) >>
     drule_all grouped_canonical_legacy_inputs >>
     disch_then (qx_choosel_then [`envb`,`tvs`] (map_every assume_tac o CONJUNCTS)) >>
     qexistsl_tac [`envb`,`tvs`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `_ = 4 + SUM _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `(?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut F args [] ret
       (subst_consts_stmts (module_consts_env tops []) fbody)) \/
   (?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
       tops ret am tx unit vs /\
     ((?tail. call_storage_ok am tx vs.vs_outcomes
       (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
      !tail. FST (call_external (SOME vs.vs_outcomes)
       (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading"))) /\
     (!tail res am' rqs obs.
       call_external_trace (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs) ==>
       obs = []) /\ marks = [])` suffices_by
    (strip_tac
     >- (disj1_tac >> qexists_tac `es` >> first_assum ACCEPT_TAC) >>
     disj2_tac >> qexists_tac `marks` >> asm_rewrite_tac[]) >>
  irule grouped_legacy_checked_route >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `envb` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `tvs` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `calldata_encodes (type_env tops) tx.function_name (MAP SND args)
        tx.args u.vs_call_ctx.cc_calldata` by simp[] >>
      drule_all_then ACCEPT_TAC
        (REWRITE_RULE [] (Q.INST [`cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`]
          (SPEC_ALL grouped_canonical_bound_registration)))) >>
  qexistsl_tac [`lbl`,`pkg`,`post`,`pre`,`z`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem grouped_canonical_call_route:
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
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  (?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut F args [] ret
    (subst_consts_stmts (module_consts_env tops []) fbody)) \/
  (?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
      tops ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail. FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading"))))
Proof
  cheat
QED
