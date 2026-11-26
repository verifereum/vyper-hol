(* Shared proof of the registration cut for the plain nonreentrant dispatch. *)
structure dispatchedRegisteredEndpointLib =
struct
open HolKernel boolLib bossLib
open defaultDispatchFactsTheory runtimeFallbackPackageEnvironmentTheory
     externalEntryBoundTheory externalBodyFrameTheory runtimeBodyShadowTheory
     runtimeEntryEndpointTheory entryStateRelTheory gasSummaryTheory
     compileEnvTheory constSubstTheory fallbackEntryEndpointTheory
     dispatchedSelectedEndpointTheory externalEntryJointTheory externalEntryChecksTheory
     externalReturnPackageTheory

(* The source body uses the same package environment as the actual fallback. *)
fun fallback_source_package_tac goal = (
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
    simp[moduleLoweringTheory.compile_register_positional_args_def, comp_return_def] >>
  `runtime_entry_body_start tops rpolicy
    ("fn___default__",cenv,[],4,mut = Payable,T,global_nonreentrant_slot,T,mut = View,
     subst_consts_stmts (module_consts_env tops []) fbody,rt) sa` by
    (pure_rewrite_tac[runtimeBodyStartDefsTheory.runtime_entry_body_start_def] >>
     disj2_tac >>
     pure_rewrite_tac[runtimeBodyStartDefsTheory.runtime_fallback_body_start_def] >>
     qpat_assum `runtime_fallback_body_start _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE
         [runtimeBodyStartDefsTheory.runtime_fallback_body_start_def]) >>
     simp[])) goal;

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
    runtime_entry_body_shadow_with_shadow_nr) >>
  (impl_tac >- asm_simp_tac bool_ss [Abbr `compiled_body`]);

fun registered_body_endpoint_tac entry_ce =
  disch_then (qx_choosel_then [`func2`,`shadow_ctx`,`shadow_func`,`cenv'`,
    `sb`,`shadow_sl`,`shadow_sb`,`shadow_unit`,`shadow_sa`,`shadow_end`]
    strip_assume_tac) >> `func2 = func` by fs[] >>
  `shadow_ctx = shadow_unit.cu_context` by fs[] >>
  qpat_x_assum `func2 = func` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_ctx = shadow_unit.cu_context` SUBST_ALL_TAC >>
  `es0.storage_trace = []` by
    (drule send_call_value_accounts >> simp[vyperInterpreterTheory.initial_state_def]) >>
  `storage_trace_domain
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) es0.storage_trace` by
    (fs[] >> EVAL_TAC >> simp[]) >>
  `runtime_body_endpoint tops rpolicy unit am tx vs es0 mut T args [] ret
      compiled_body` by
    (PURE_REWRITE_TAC [runtime_body_endpoint_def] >>
     qexistsl_tac ([`[]`,entry_ce] @ [`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`,
       `shadow_unit`,`shadow_func`,`shadow_sa`,`shadow_end`]) >>
     fs[Abbr `compiled_body`, gas_explicit_def] >>
     gvs[GSYM bodyPtrDefsTheory.ghost_inv_cx_dead] >>
     qexistsl_tac [`bindings`,`env_t`,`env'`] >> asm_rewrite_tac[]);

val split_dispatch_tac =
  strip_tac >> drule default_dispatch_raw_cases >>
  disch_then (DISJ_CASES_THEN2
    (MAP_EVERY ASSUME_TAC o CONJUNCTS)
    (qx_choosel_then [`tys`,`tvs`] strip_assume_tac));

fun fallback_registration_tac goal = (
  drule_all fallback_entry_registration_joint >>
  disch_then (qx_choosel_then
    [`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`,`rt`] strip_assume_tac) >>
  fallback_source_package_tac >>
  qpat_x_assum `rt = if ret = NoneT then NONE else SOME ret` SUBST_ALL_TAC >>
  drule_all entry_path_endpoint_facts >> strip_tac >>
  mp_tac (Q.SPECL [`unit.cu_context`,`func`,`vs`,`s0`,`bb`]
    entry_context_continuation) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `cenv with ce_vars := cenv.ce_vars = cenv` by simp[compile_env_component_equality] >>
  `!id ty. MEM (id,ty) args ==>
     (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
     cenv.ce_var_type id = SOME ty` by
    (qpat_assum `args = []` (fn eq => simp_tac (srw_ss()) [eq])) >>
  `!id loc. FLOOKUP cenv.ce_vars id = SOME loc ==> MEM id (MAP FST args)` by
    (rpt strip_tac >> drule_all external_entry_target_declared >> simp[]) >>
  qunabbrev_tac `rr` >> bound_source_tac >>
  registered_body_frame_tac (`"fn___default__"`,`cenv`,`[]`,`4`,
    `mut = Payable`,`if ret = NoneT then NONE else SOME ret`)) goal;

fun fallback_endpoint_tac goal = (
  registered_body_shadow_tac [`"fn___default__"`,`cenv`,`[]`,`4`,
    `mut = Payable`,`T`,`global_nonreentrant_slot`,`T`,`mut = View`,
    `compiled_body`,`if ret = NoneT then NONE else SOME ret`,`sa`] >>
  registered_body_endpoint_tac `cenv` >> qunabbrev_tac `compiled_body` >>
  qpat_x_assum `args = []` SUBST_ALL_TAC) goal;

fun selected_registration_tac goal = (
  SUBGOAL_THEN (Parse.Term `?ts. FIND (\(name,ts). abi_method_id (type_env tops) name ts =
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
    (drule compile_register_positional_args_cenv >> simp[compile_env_component_equality]) >>
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
    `is_payable`,`if ret = NoneT then NONE else SOME ret`)) goal;

fun selected_endpoint_tac goal = (
  `~EXISTS external_has_defaults (FST (classify_functions tops))` by
    (qpat_assum `EVERY _ (FST (classify_functions tops))` mp_tac >>
     simp_tac (srw_ss()) [listTheory.EXISTS_NOT_EVERY, combinTheory.o_DEF]) >>
  registered_body_shadow_tac [`lbl`,`cenv0`,`pos_args`,`min_cds`,
    `is_payable`,`T`,`global_nonreentrant_slot`,`T`,`mut = View`,
    `compiled_body`,`if ret = NoneT then NONE else SOME ret`,`st`] >>
  registered_body_endpoint_tac `cenv0` >> qunabbrev_tac `compiled_body`) goal;
end
