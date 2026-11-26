(* Assemble dispatched calls once the selected entry reaches the body. *)
Theory dispatchedCallAssembly
Ancestors
  dispatchedArgsBind dispatchedEntryValueRevert fallbackEntryEndpoint
  loweringRuntimeCorrect gasShadowRunLowering loweringShapeProps
  gasShadowUnit sourceUnitExecution dispatchedSelectedEndpoint
  defaultDispatchFacts externalReturnPackage runtimeFallbackPackageEnvironment
  externalEntryValueRevert externalEntryBound vyperLoweringCorrect fragGasPathMem gasSummary
  externalBodyFrame externalEntryJoint externalEntryChecks runtimeBodyShadow
  runtimeEntryEndpoint entryStateRel compileEnv constSubst
  vyperStorageFootprint vyperStorageTrace
Libs
  dispatchedRegisteredEndpointLib

Triviality legacy_runtime_shadow_context[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit ==>
  gas_shadow_context unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  `?shadow. runtime_gas_shadow_unit tops rpolicy = SOME shadow /\
            gas_shadow_unit unit shadow` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     irule runtime_gas_shadow_unit_exists >> fs[]) >>
  gvs[gas_shadow_unit_def]
QED

Theorem dispatched_call_correct_from_value_success:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) /\
    (!env es0. bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
         tops ret am tx unit vs) ==>
    source_unit_execution_correct tops ret am tx unit vs /\
    ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx unit vs
Proof
  rpt gen_tac >> strip_tac >> conj_asm2_tac
  >- (simp[source_unit_execution_correct_def,
           source_unit_execution_correct_at_def] >>
      qpat_x_assum `?marks. _` (qx_choose_then `marks` assume_tac) >>
      qexistsl_tac [`marks`, `shadow_unit.cu_context`] >> simp[]) >>
  drule_all dispatched_vyper_call_bind >>
  disch_then (qx_choose_then `env` assume_tac) >>
  namedCases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>)`
    ["res es0"] >>
  reverse (namedCases_on `res` ["u", "e"])
  >- (qexists_tac `[]` >>
      `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
        (drule_all legacy_runtime_shadow_context >> simp[]) >>
      drule_all external_entry_value_revert_dispatched_with_nr >> simp[]) >>
  Cases_on `u` >>
  qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]
QED

Theorem dispatched_call_correct_from_selected_endpoint:
  !tops rpolicy unit shadow_unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    (!env es0. tx.function_name <> "__default__" /\
       bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)) ==>
    source_unit_execution_correct tops ret am tx unit vs /\
    ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx unit vs
Proof
  rpt gen_tac >> strip_tac >>
  irule dispatched_call_correct_from_value_success >>
  asm_rewrite_tac [] >> conj_tac
  >- (qexists_tac `rpolicy` >> asm_rewrite_tac []) >>
  qexistsl_tac [`args`, `fbody`, `mut`, `F`] >>
  asm_rewrite_tac [] >> rpt gen_tac >> strip_tac >>
  `runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)` by
    (Cases_on `tx.function_name = "__default__"`
     >- (drule_all dispatched_entry_endpoint_default >> simp[]) >>
     qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]) >>
  drule_all runtime_body_joint_from_start_with_shadow >> simp[]
QED

Theorem dispatched_nonreentrant_result[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s) /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
    SOME (tx.function_name,tx.args) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) ==>
  ?shadow_unit marks.
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_unit_execution_correct_with shadow_unit.cu_context marks
      tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  split_dispatch_tac
  >- (fallback_registration_tac >> fallback_endpoint_tac >>
      drule_all runtime_body_endpoint_correct >> disch_then ACCEPT_TAC) >>
  selected_registration_tac >> selected_endpoint_tac >>
  drule_all runtime_body_endpoint_correct >> disch_then ACCEPT_TAC
QED

Triviality dispatched_call_readings_from_value_success:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) /\
    (!env es0. bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
         tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))) ==>
    ?marks.
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dispatched_vyper_call_bind >>
  disch_then (qx_choose_then `env` assume_tac) >>
  namedCases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>)`
    ["res es0"] >>
  reverse (namedCases_on `res` ["u", "e"])
  >- (qexists_tac `[]` >>
      `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
        (drule_all legacy_runtime_shadow_context >> simp[]) >>
      conj_tac >- (drule_all external_entry_value_revert_dispatched_with_nr >> simp[]) >>
      `value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
      drule_all external_entry_reject_readings_nr >> simp[]) >>
  Cases_on `u` >>
  qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]
QED

Triviality dispatched_call_readings_from_selected_endpoint:
  !tops rpolicy unit shadow_unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    (!env es0. tx.function_name <> "__default__" /\
       bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)) ==>
    ?marks.
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >>
  irule dispatched_call_readings_from_value_success >>
  asm_rewrite_tac [] >> conj_tac
  >- (qexists_tac `rpolicy` >> asm_rewrite_tac []) >>
  qexistsl_tac [`args`, `fbody`, `mut`, `F`] >>
  asm_rewrite_tac [] >> rpt gen_tac >> strip_tac >>
  `runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)` by
    (Cases_on `tx.function_name = "__default__"`
     >- (drule_all dispatched_entry_endpoint_default >> simp[]) >>
     qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]) >>
  drule_all runtime_body_joint_from_start_with_readings >> simp[]
QED

Theorem dispatched_call_correct_with_readings:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) ==>
    ?marks.
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `nr`
  >- (irule dispatched_call_readings_from_value_success >> asm_rewrite_tac[] >>
      conj_tac >- (qexists_tac `rpolicy` >> asm_rewrite_tac[]) >>
      qexistsl_tac [`args`,`fbody`,`mut`,`T`] >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      drule_all dispatched_nonreentrant_result >>
      disch_then (qx_choosel_then [`actual_shadow`,`marks`] strip_assume_tac) >>
      qexists_tac `marks` >> gvs[]) >>
  drule_at (Pat `runtime_gas_shadow_unit _ _ = _`)
    dispatched_call_readings_from_selected_endpoint >>
  disch_then (drule_at (Pat `vyperInterpreter$lookup_function _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`unit`,`am`,`vs`] mp_tac) >>
  fs[dispatched_entry_endpoint_selected] >>
  disch_then (fn result => first_assum (ACCEPT_TAC o MATCH_MP result))
QED

Theorem dispatched_call_correct:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) ==>
    source_unit_execution_correct tops ret am tx unit vs /\
    ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx unit vs
Proof
  metis_tac[dispatched_call_correct_with_readings,
            source_unit_execution_correct_def,
            source_unit_execution_correct_at_def]
QED
