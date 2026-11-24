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

(* Use the same source binding and value check in each route projection. *)
val dispatched_source_value_cases_tac =
  drule_all dispatched_vyper_call_bind >>
  disch_then (qx_choose_then `env` assume_tac) >>
  namedCases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>)`
    ["res es0"] >>
  reverse (namedCases_on `res` ["u", "e"]);

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
  dispatched_source_value_cases_tac
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

Triviality fallback_runtime_body_start:
  runtime_fallback_body_start tops rpolicy
    (lbl,cenv,[],4,pay,nr,nkey,ut,iv,fbody,rt) st ==>
  runtime_entry_body_start tops rpolicy
    ("fn___default__",cenv,[],4,pay,nr,nkey,ut,iv,fbody,rt) st
Proof
  simp[runtimeBodyStartDefsTheory.runtime_entry_body_start_def,
       runtimeBodyStartDefsTheory.runtime_fallback_body_start_def]
QED

(* The source body uses the same package environment as the actual fallback. *)
val fallback_source_package_tac =
  `vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,T,args,[],ret,fbody)` by
    (qpat_assum `tx.function_name = "__default__"` (fn name_eq =>
       qpat_assum `vyperInterpreter$lookup_function NONE tx.function_name External tops = _`
         (ACCEPT_TAC o REWRITE_RULE [name_eq]))) >>
  `args = []` by metis_tac[default_fallback_no_args] >>
  drule_all default_fallback_classified >>
  strip_tac >>
  qabbrev_tac `rr = lookup_raw_return_or_F (NONE:num option) "__default__" External tops` >>
  `set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot)
      (SOME (mut,T,rr,"__default__",[],([]:expr list),ret,
        subst_consts_stmts (module_consts_env tops []) fbody))) =
      SOME (cenv,mut = Payable,T,global_nonreentrant_slot,T,mut = View,
        subst_consts_stmts (module_consts_env tops []) fbody,rt)` by
    (qpat_assum `runtime_fallback_body_start _ _ _ _`
      (mp_tac o REWRITE_RULE [runtimeBodyStartDefsTheory.runtime_fallback_body_start_def]) >>
     rpt strip_tac >> gvs[]) >>
  drule fallback_empty_source_external_package >> strip_tac >>
  `compile_register_positional_args cenv [] 4 sa = (cenv,sa)` by
    simp[moduleLoweringTheory.compile_register_positional_args_def, compileEnvTheory.comp_return_def] >>
  drule_then assume_tac fallback_runtime_body_start;

val bound_source_tac =
  drule_all external_entry_bound_no_defaults >> strip_tac >>
  `external_entry_bound tops am tx vs.vs_outcomes es0.gas_obs mut args [] es0` by
    (`es0 with gas_obs := es0.gas_obs = es0` by (Cases_on `es0` >> simp[]) >>
     pop_assum (fn same =>
       qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
         (qspec_then `es0.gas_obs` (ACCEPT_TAC o PURE_REWRITE_RULE [same]))));

fun registered_body_frame_tac (lbl,entry_ce,pos_args,min_cds,payable,rt) =
  mp_tac (Q.SPECL ([`tops`,`rpolicy`,`unit`,`am`,`tx`,`ret`,`vs`,`mut`,`T`,
    `args`,`[]`,`fbody`,`es0.gas_obs`,`es0`,lbl,entry_ce,pos_args,min_cds,payable] @
    [`global_nonreentrant_slot`,`T`,`mut = View`,rt,`cenv`]) external_source_body_frame_nr) >>
  impl_tac >-
    (asm_simp_tac (srw_ss()) [subst_consts_expr_def] >>
     rpt conj_tac >>
     rpt strip_tac >>
     qpat_assum `!id ty. MEM (id,ty) args ==> (_ /\ _)`
       (qspecl_then [`id`,`ty`] mp_tac) >>
     simp[]) >>
  strip_tac;

(* The code and source frames are ready before the lock executes. *)
fun registered_body_shadow_tac placement =
  drule_all nonreentrantEntryPathTheory.guarded_body_code_from_registration >>
  simp[] >>
  disch_then (qx_choosel_then [`sl`,`se`] strip_assume_tac) >>
  qabbrev_tac `compiled_body = subst_consts_stmts (module_consts_env tops []) fbody` >>
  mp_tac (Q.SPECL ([`tops`,`rpolicy`,`unit`] @ placement @
    [`cenv`,`sa`,`sl`,`st'`,`bindings`,`unit.cu_context`,
     `initial_evaluation_context am.sources am.layouts tx NONE`,`env_t`,`env'`,`ret`])
    runtime_entry_body_shadow_with_shadow_nr);

fun registered_body_endpoint_tac entry_ce =
  disch_then (qx_choosel_then [`func2`,`shadow_ctx`,`shadow_func`,`cenv'`,
    `sb`,`shadow_sl`,`shadow_sb`,`shadow_unit`,`shadow_sa`,`shadow_end`]
    strip_assume_tac) >> `func2 = func` by fs[] >>
  `shadow_ctx = shadow_unit.cu_context` by fs[] >>
  qpat_x_assum `func2 = func` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_ctx = shadow_unit.cu_context` SUBST_ALL_TAC >>
  `es0.storage_trace = []` by
    (drule entryStateRelTheory.send_call_value_accounts >> simp[vyperInterpreterTheory.initial_state_def]) >>
  `storage_trace_domain
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) es0.storage_trace` by
    (fs[] >> EVAL_TAC >> simp[]) >>
  `runtime_body_endpoint tops rpolicy unit am tx vs es0 mut T args [] ret
      compiled_body` by
    (PURE_REWRITE_TAC [runtime_body_endpoint_def] >>
     qexistsl_tac ([`[]`,entry_ce] @ [`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`,
       `shadow_unit`,`shadow_func`,`shadow_sa`,`shadow_end`]) >>
     fs[Abbr `compiled_body`, gas_explicit_def] >> rpt conj_tac >>
     TRY (qexistsl_tac [`bindings`,`env_t`,`env'`] >> asm_rewrite_tac[] >> NO_TAC) >>
     gvs[GSYM bodyPtrDefsTheory.ghost_inv_cx_dead] >>
     rpt strip_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ /\ ghost_inv H _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >> simp[]);

Triviality dispatched_nonreentrant_endpoint:
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
  runtime_body_endpoint tops rpolicy unit am tx vs es0 mut T args [] ret
    (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  strip_tac >>
  drule default_dispatch_raw_cases >>
  disch_then (DISJ_CASES_THEN2
    (MAP_EVERY ASSUME_TAC o CONJUNCTS)
    (qx_choosel_then [`tys`,`tvs`] strip_assume_tac))
  >- (drule_all fallback_entry_registration_joint >>
      disch_then (qx_choosel_then
        [`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`,`rt`] strip_assume_tac) >>
      fallback_source_package_tac >>
      qpat_x_assum `rt = if ret = NoneT then NONE else SOME ret` SUBST_ALL_TAC >>
      drule_all entry_path_endpoint_facts >> strip_tac >>
      mp_tac (Q.SPECL [`unit.cu_context`,`func`,`vs`,`s0`,`bb`]
        entry_context_continuation) >>
      impl_tac >- asm_rewrite_tac[] >> strip_tac >>
      `cenv with ce_vars := cenv.ce_vars = cenv` by simp[compile_env_component_equality] >>
      `!id ty. MEM (id,ty) args ==>
         (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
         cenv.ce_var_type id = SOME ty` by
        (qpat_assum `args = []` (fn eq => simp_tac (srw_ss()) [eq])) >>
      `!id loc. FLOOKUP cenv.ce_vars id = SOME loc ==> MEM id (MAP FST args)` by
        (rpt strip_tac >> drule_all external_entry_target_declared >> simp[]) >>
      qunabbrev_tac `rr` >>
      bound_source_tac >>
      registered_body_frame_tac (`"fn___default__"`,`cenv`,`[]`,`4`,
        `mut = Payable`,`if ret = NoneT then NONE else SOME ret`) >>
      registered_body_shadow_tac [`"fn___default__"`,`cenv`,`[]`,`4`,
        `mut = Payable`,`T`,`global_nonreentrant_slot`,`T`,`mut = View`,
        `compiled_body`,`if ret = NoneT then NONE else SOME ret`,`sa`] >>
      impl_tac >- asm_simp_tac bool_ss [Abbr `compiled_body`] >>
      registered_body_endpoint_tac `cenv` >>
      qpat_x_assum `args = []` SUBST_ALL_TAC >>
      qunabbrev_tac `compiled_body` >> first_assum ACCEPT_TAC) >>
  SUBGOAL_THEN (Term `?ts. FIND (\(name,ts). abi_method_id (type_env tops) name ts =
      cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
      SOME (tx.function_name,ts)`) ASSUME_TAC
  >- (qexists_tac `tys` >> first_assum ACCEPT_TAC) >>
  drule_all dispatched_selected_registration_joint >>
  disch_then (qx_choosel_then
    [`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,
     `rt`,`st`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`] strip_assume_tac) >>
  `nkey = global_nonreentrant_slot /\ ut' = T /\ iv = (mut = View) /\
    rt = (if ret = NoneT then NONE else SOME ret)` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> simp[]) >>
  gvs[] >>
  `runtime_entry_body_start tops rpolicy
    (lbl,cenv0,pos_args,min_cds,is_payable,T,global_nonreentrant_slot,
     T,mut = View,subst_consts_stmts (module_consts_env tops []) fbody,
     if ret = NoneT then NONE else SOME ret) st` by
    (pure_rewrite_tac[runtimeBodyStartDefsTheory.runtime_entry_body_start_def] >>
     disj1_tac >> first_assum ACCEPT_TAC) >>
  `cenv with ce_vars := cenv0.ce_vars = cenv0` by
    (drule compile_register_positional_args_cenv >>
     simp[compile_env_component_equality]) >>
  drule_all supportedGetterPropsTheory.supported_selected_external_body >> strip_tac >>
  drule_all external_selected_args_distinct >> strip_tac >>
  `!id ty. MEM (id,ty) args ==>
     (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
     cenv.ce_var_type id = SOME ty` by
    (rpt strip_tac
     >- (drule_all external_entry_target_param_pointer >> simp[]) >>
     drule_all external_entry_target_param_type >> simp[]) >>
  `!id loc. FLOOKUP cenv.ce_vars id = SOME loc ==> MEM id (MAP FST args)` by
    (rpt strip_tac >> drule_all external_entry_target_declared >> simp[]) >>
  bound_source_tac >>
  registered_body_frame_tac (`lbl`,`cenv0`,`pos_args`,`min_cds`,
    `is_payable`,`if ret = NoneT then NONE else SOME ret`) >>
  `~EXISTS external_has_defaults (FST (classify_functions tops))` by
    (qpat_assum `EVERY _ (FST (classify_functions tops))` mp_tac >>
     simp_tac (srw_ss()) [listTheory.EXISTS_NOT_EVERY, combinTheory.o_DEF]) >>
  registered_body_shadow_tac [`lbl`,`cenv0`,`pos_args`,`min_cds`,
    `is_payable`,`T`,`global_nonreentrant_slot`,`T`,`mut = View`,
    `compiled_body`,`if ret = NoneT then NONE else SOME ret`,`st`] >>
  impl_tac >- asm_simp_tac bool_ss [Abbr `compiled_body`] >>
  registered_body_endpoint_tac `cenv0` >>
  qunabbrev_tac `compiled_body` >> first_assum ACCEPT_TAC
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
  strip_tac >>
  drule_all dispatched_nonreentrant_endpoint >> strip_tac >>
  drule_all runtime_body_endpoint_correct >> simp[]
QED

(* Before body correctness: pass the selected value refusal or the actual
   registered body endpoint to its own continuation. *)
Theorem dispatched_selected_route_cases:
  !tops rpolicy unit am tx ret vs mut nr args fbody Q.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) /\
    (!env es0 e.
       bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
         (INR e,es0) ==> Q) /\
    (!env es0.
       bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
         (INL (),es0) /\
       runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args [] ret
         (subst_consts_stmts (module_consts_env tops []) fbody) ==> Q) ==>
    Q
Proof
  rpt gen_tac >> strip_tac >> dispatched_source_value_cases_tac
  >- (qpat_x_assum `!env es0 e. _`
        (qspecl_then [`env`, `es0`, `e`] mp_tac) >> simp[]) >>
  Cases_on `u` >>
  `runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args [] ret
     (subst_consts_stmts (module_consts_env tops []) fbody)` by
    (Cases_on `nr`
     >- (drule_all dispatched_nonreentrant_endpoint >> simp[]) >>
     `runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
       (subst_consts_stmts (module_consts_env tops []) fbody)` by
       (Cases_on `tx.function_name = "__default__"`
        >- (drule_all dispatched_entry_endpoint_default >> simp[]) >>
        drule_all dispatched_entry_endpoint_selected >> simp[]) >>
     drule_all runtime_entry_endpoint_body_endpoint >> simp[]) >>
  qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]
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
  dispatched_source_value_cases_tac
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
