(* Source-side facts at the entry of the external function body that
   valid_vyper_call selects: its typing, the state send_call_value leaves,
   and the typing context that state is consistent with.  Shared by the S1
   pieces external_body_source_ok and external_body_frame. *)
Theory externalBodySupport
Ancestors
  list pair finite_map rich_list externalEntryBound
  vyperCheckedRuntimeWriteSafety vyperRuntimeWriteSafetyFrame
  vyperExternalDefaultsFiniteStorage vyperExternalEntryStorageFrame vyperStorageFootprint
  vyperEvalOutcomeSuffix
  e2eDefs supportedProgram supportedDecls compileVyper constSubst constSubstCorrect constSubstStmts
  vyperTypeSystem vyperTypeInvariants vyperTypeContract vyperTypeContractFunction
  vyperTypeContractContext vyperTypeContractSoundness vyperTypeContractGetter
  vyperTypeExternalDefaults vyperTypeInitialState vyperTypeBindArguments vyperTypeCallStackSoundness
  vyperInterpreter vyperGetter vyperReadOnlySyntax vyperState vyperContext

Theorem external_lookup_body_typing_canonical:
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, nr, args, dflts, ret, fbody) ==>
  ?art env_t env'.
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    checked_contract_runtime_ready art [(NONE,tops)] am tx /\
    env_t = function_entry_env art [(NONE,tops)] NONE External args /\
    env_t.current_src = NONE /\
    env_t.type_defs = get_tenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    env_t.fn_sigs = art.cta_fn_sigs /\
    env_t.bare_globals = art.cta_bare_globals /\
    env_t.bare_global_assignable = art.cta_bare_global_assignable /\
    env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env_t.flag_members = art.cta_flag_members /\
    type_stmts env_t ret fbody = SOME env' /\
    (!id ty. MEM (id,ty) args ==>
      FLOOKUP env_t.var_types id = SOME ty /\
      IS_SOME (FLOOKUP env_t.var_assignable id)) /\
    (!n ty. FLOOKUP env_t.var_types n = SOME ty ==>
      MEM (n,ty) args) /\
    (!n b. FLOOKUP env_t.var_assignable n = SOME b ==>
      ?ty. MEM (n,ty) args) /\
    stmts_no_control_escape fbody /\
    (ret <> NoneT ==> stmts_no_fallthrough fbody) /\
    call_evaluation_safe
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (int_calls_stmts fbody)
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
   layouts_agree tops am tx` by fs[source_deployment_rel_def] >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  qpat_x_assum `source_deployment_rel _ _ _` kall_tac >>
  qpat_x_assum `source_typing_ok _ _ _` kall_tac >>
  gvs[] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
     External mut nr args dflts ret fbody` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     qexistsl [`tx.function_name`, `raw`] >> simp[]) >>
  `call_evaluation_safe
     (initial_evaluation_context am.sources am.layouts tx NONE)
     (int_calls_stmts fbody)` by
    (drule checked_explicit_external_body_call_evaluation_safe >>
     simp[] >> disch_then drule >> simp[]) >>
  `ALL_DISTINCT (MAP FST args) /\ stmts_no_control_escape fbody /\
   (ret <> NoneT ==> stmts_no_fallthrough fbody) /\
   IS_SOME (type_stmts (function_entry_env art [(NONE,tops)] NONE External args)
              ret fbody)` by fs[check_function_body_def, params_ok_def] >>
  Cases_on `type_stmts (function_entry_env art [(NONE,tops)] NONE External args)
             ret fbody` >> gvs[] >>
  gvs[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static,
      get_tenv_def, initial_evaluation_context_def] >>
  rw[]
  >- (drule_all FOLDL_extend_local_args_formal_lookup >> simp[])
  >- (drule_all FOLDL_extend_local_args_formal_lookup >> simp[])
  >- (drule_all FOLDL_extend_local_args_var_types_range >> simp[])
  >- (drule_all FOLDL_extend_local_args_var_assignable_range >> simp[] >> metis_tac[])
  ) >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
   layouts_agree tops am tx` by fs[source_deployment_rel_def] >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  qpat_x_assum `source_deployment_rel _ _ _` kall_tac >>
  qpat_x_assum `source_typing_ok _ _ _` kall_tac >>
  gvs[] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all checked_public_getter_body_typing_package >> strip_tac >>
  `?exp. fbody = [Return (SOME exp)]` by
    (Cases_on `decl` >>
     gvs[is_public_getter_decl_def, external_getter_tuple_def] >>
     Cases_on `v` >>
     gvs[external_getter_tuple_def, getter_def, AllCaseEqs()] >>
     rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `int_calls_stmts fbody = []` by
    metis_tac[selected_public_getter_body_int_calls_empty] >>
  `call_evaluation_safe
     (initial_evaluation_context am.sources am.layouts tx NONE) []` by
    (`(initial_evaluation_context am.sources am.layouts tx NONE) =
       ((initial_evaluation_context am.sources am.layouts tx NONE) with
         stk := [(NONE,tx.function_name)])` by
       simp[initial_evaluation_context_def] >>
     pop_assum SUBST1_TAC >>
     irule (INST_TYPE [``:'a`` |-> ``:num``]
       checked_contract_call_evaluation_safe_singleton) >>
     qexistsl [`art`, `am.layouts`, `[(NONE,tops)]`] >>
     simp[initial_evaluation_context_def, calls_follow_call_graph_def]) >>
  gvs[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static,
       get_tenv_def, initial_evaluation_context_def,
       stmt_no_control_escape_def, stmt_no_fallthrough_def] >>
  metis_tac[]
QED

Theorem external_lookup_body_typing:
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, nr, args, dflts, ret, fbody) ==>
  ?art env_t env'.
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    checked_contract_runtime_ready art [(NONE,tops)] am tx /\
    env_t.current_src = NONE /\
    env_t.type_defs = get_tenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    env_t.fn_sigs = art.cta_fn_sigs /\
    env_t.bare_globals = art.cta_bare_globals /\
    env_t.bare_global_assignable = art.cta_bare_global_assignable /\
    env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env_t.flag_members = art.cta_flag_members /\
    type_stmts env_t ret fbody = SOME env' /\
    (!id ty. MEM (id,ty) args ==>
      FLOOKUP env_t.var_types id = SOME ty /\
      IS_SOME (FLOOKUP env_t.var_assignable id)) /\
    (!n ty. FLOOKUP env_t.var_types n = SOME ty ==>
      MEM (n,ty) args) /\
    (!n b. FLOOKUP env_t.var_assignable n = SOME b ==>
      ?ty. MEM (n,ty) args) /\
    stmts_no_control_escape fbody /\
    (ret <> NoneT ==> stmts_no_fallthrough fbody) /\
    call_evaluation_safe
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (int_calls_stmts fbody)
Proof
  strip_tac >> drule_all external_lookup_body_typing_canonical >> strip_tac >>
  qexistsl [`art`, `env_t`, `env'`] >> asm_rewrite_tac[]
QED

Theorem external_selected_body_typing:
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, F, args, [], ret, fbody) ==>
  ?art env_t env'.
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    checked_contract_runtime_ready art [(NONE,tops)] am tx /\
    env_t.current_src = NONE /\
    env_t.type_defs = get_tenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    env_t.fn_sigs = art.cta_fn_sigs /\
    env_t.bare_globals = art.cta_bare_globals /\
    env_t.bare_global_assignable = art.cta_bare_global_assignable /\
    env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env_t.flag_members = art.cta_flag_members /\
    type_stmts env_t ret fbody = SOME env' /\
    (!id ty. MEM (id,ty) args ==>
      FLOOKUP env_t.var_types id = SOME ty /\
      IS_SOME (FLOOKUP env_t.var_assignable id)) /\
    (!n ty. FLOOKUP env_t.var_types n = SOME ty ==>
      MEM (n,ty) args) /\
    (!n b. FLOOKUP env_t.var_assignable n = SOME b ==>
      ?ty. MEM (n,ty) args) /\
    stmts_no_control_escape fbody /\
    (ret <> NoneT ==> stmts_no_fallthrough fbody) /\
    call_evaluation_safe
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (int_calls_stmts fbody)
Proof
  strip_tac >> drule_all external_lookup_body_typing >>
  disch_then ACCEPT_TAC
QED

Theorem external_send_call_value_frame:
  send_call_value mut cx st = (res,st') ==>
  st' with accounts := st.accounts = st
Proof
  rw[send_call_value_def, transfer_value_def, bind_def, ignore_bind_def,
     get_accounts_def, check_def, assert_def, update_accounts_def,
     return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem external_body_lock_frame:
  !cx nr iv es es'.
    lock_if_nr cx nr iv es = (INL (),es') ==>
    es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
    es'.accounts = es.accounts /\ es'.outcomes = es.outcomes
Proof
  PURE_REWRITE_TAC [lock_if_nr_def] >>
  ACCEPT_TAC vyperTypeEvalProofsTheory.intcall_lock_state_preserves_frame
QED

Theorem external_body_prefix_state:
  machine_well_typed am /\
  bind_arguments tenv args vals = SOME env /\
  send_call_value mut cx
    (initial_state am [env] with <|outcomes := SOME os; requests := []|>) =
    (INL (),es0) ==>
  es0.scopes = [env] /\ es0.immutables = am.immutables /\
  es0.outcomes = SOME os /\ es0.requests = [] /\
  state_well_typed es0 /\ accounts_well_typed es0.accounts
Proof
  strip_tac >>
  `scope_well_typed env` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `accounts_well_typed es0.accounts` by
    (irule send_call_value_accounts_well_typed_c53 >>
     goal_assum (drule_at Any) >>
     simp[initial_state_accounts_well_typed_simple]) >>
  drule external_send_call_value_frame >>
  simp[evaluation_state_component_equality, initial_state_def] >>
  strip_tac >> gvs[state_well_typed_def, machine_well_typed_def]
QED

Theorem external_selected_env_consistent:
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  checked_contract_runtime_ready art [(NONE,tops)] am tx /\
  env_t.current_src = NONE /\
  env_t.type_defs = get_tenv
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  env_t.fn_sigs = art.cta_fn_sigs /\
  env_t.bare_globals = art.cta_bare_globals /\
  env_t.bare_global_assignable = art.cta_bare_global_assignable /\
  env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env_t.flag_members = art.cta_flag_members /\
  (!id ty. MEM (id,ty) args ==>
    FLOOKUP env_t.var_types id = SOME ty /\
    IS_SOME (FLOOKUP env_t.var_assignable id)) /\
  (!n ty. FLOOKUP env_t.var_types n = SOME ty ==> MEM (n,ty) args) /\
  (!n b. FLOOKUP env_t.var_assignable n = SOME b ==>
    ?ty. MEM (n,ty) args) /\
  bind_arguments (type_env tops) args vals = SOME env /\
  es0.scopes = [env] /\ es0.immutables = am.immutables ==>
  env_consistent env_t
    (initial_evaluation_context am.sources am.layouts tx NONE) es0
Proof
  strip_tac >> gvs[checked_contract_runtime_ready_def] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art [(NONE,tops)] NONE` >>
      rpt (conj_tac >-
        simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_src >> simp[])
  >- (`es0 with scopes := [env] = es0` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (SUBST1_TAC o GSYM) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env tops`, `vals`] >>
      simp[get_tenv_def, initial_evaluation_context_def,
           type_env_all_modules_def, type_env_def] >> metis_tac[])
  >- (gvs[env_immutables_consistent_def] >> rw[] >>
      qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
      simp[immutables_ready_def] >> strip_tac >>
      first_x_assum drule_all >> simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`id_str`, `tv`, `v`] mp_tac) >> simp[])
QED

Theorem external_source_context_typed:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx ==>
  context_well_typed
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  functions_well_typed
    (initial_evaluation_context am.sources am.layouts tx NONE)
Proof
  strip_tac >> drule_all source_typing_ok_runtime_ready >> strip_tac >>
  conj_tac
  >- gvs[call_tx_well_typed_def, context_well_typed_def,
         initial_evaluation_context_def] >>
  irule check_contract_functions_well_typed_initial >>
  gvs[checked_contract_runtime_ready_def] >> goal_assum (drule_at Any) >> simp[]
QED

(* Successful defaults preserve the checked immutable frame and leave a
   well-typed state for binding the external function's arguments. *)
Theorem external_entry_bound_source_frame:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  external_entry_bound tops am tx os gs mut args dflts es ==>
  (?vals env. bind_arguments (type_env tops) args vals = SOME env /\
              es.scopes = [env]) /\
  outcome_suffix (SOME os) es.outcomes /\
  es.immutables = am.immutables /\ state_well_typed es /\
  accounts_well_typed es.accounts /\
  !H. valid_horizon
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H es.storage_trace ==>
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE) es (FST H)
Proof
  strip_tac >>
  qpat_x_assum `external_entry_bound _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [external_entry_bound_def]) >>
  conj_tac >- (qexistsl [`tx.args ++ dflt_vs`, `env`] >> simp[]) >>
  conj_tac
  >- (`s1.outcomes = SOME os` by
        (drule external_send_call_value_frame >>
         simp[evaluation_state_component_equality, initial_state_def]) >>
      qpat_assum `eval_external_defaults _ _ _ = _` mp_tac >>
      simp_tac std_ss [eval_external_defaults_run, LET_THM] >> pairarg_tac >>
      simp[] >> strip_tac >>
      qpat_assum `rt with scopes := _ = s2` (SUBST1_TAC o SYM) >>
      simp[] >> drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `cx = initial_evaluation_context am.sources am.layouts tx NONE` by simp[Abbr `cx`] >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  drule_all external_source_context_typed >>
  disch_then (strip_assume_tac o REWRITE_RULE
    [GSYM (ASSUME ``cx = initial_evaluation_context am.sources am.layouts tx NONE``)]) >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
   find_function_module am tx.target tx.function_name = NONE /\
   lookup_exported_function cx am tx.function_name = SOME (mut,nr,args,dflts,ret,fbody)` by
    fs[Abbr `cx`, source_deployment_rel_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def] >>
  `get_module_code cx NONE = SOME tops` by
    (qpat_assum `cx = initial_evaluation_context _ _ _ _` SUBST1_TAC >>
     drule_then (ACCEPT_TAC o CONJUNCT2) source_deployment_context) >>
  `~cx.in_deploy` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  `s1.immutables = am.immutables /\ s1.scopes = [FEMPTY] /\
   state_well_typed s1 /\ accounts_well_typed s1.accounts` by
    (`accounts_well_typed s1.accounts` by
       (irule send_call_value_accounts_well_typed_c53 >>
        goal_assum (drule_at Any) >>
        irule initial_state_accounts_well_typed >> simp[]) >>
     drule external_send_call_value_frame >>
     simp[evaluation_state_component_equality, initial_state_def] >>
     strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`machine_well_typed am`, `s1.immutables = am.immutables`,
        `s1.scopes = [FEMPTY]`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[state_well_typed_def, machine_well_typed_def, scope_well_typed_def]) >>
  `s2.immutables = s1.immutables` by
    (mp_tac (Q.SPECL [`am`,`tx`,`tops`,`art`,`NONE`,`tops`,`mut`,`nr`,`args`,
       `dflts`,`ret`,`fbody`] checked_singleton_runtime_write_safety) >>
     impl_tac >- fs[Abbr `cx`] >>
     qpat_assum `Abbrev (cx = _)` (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     strip_tac >>
     qpat_assum `eval_external_defaults _ _ _ = _` mp_tac >>
     simp_tac std_ss [eval_external_defaults_run, LET_THM] >> pairarg_tac >>
     simp[] >> strip_tac >>
     qpat_x_assum `rt with scopes := _ = s2` (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) [] >>
     qpat_x_assum `res = INL dflt_vs` SUBST_ALL_TAC >>
     qpat_assum `s1.immutables = _` (SUBST1_TAC o SYM) >>
     qspecl_then [`cx`, `DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts`]
       mp_tac (Q.INST [`R` |-> `R`] (cj 6 runtime_writes_frame_mutual)) >>
     impl_tac >- simp[EVERY_DROP] >>
     disch_then (qspecl_then [`s1 with scopes := [FEMPTY]`, `INL dflt_vs`, `rt`]
       mp_tac) >> simp[]) >>
  `!regions : (bool # bytes32 # type_value) list.
     storage_well_formed_on cx (initial_state am []) regions ==>
     storage_well_formed_on cx s1 regions` by
    (gen_tac >> disch_tac >>
     drule_at (Pat `send_call_value _ _ _ = _`)
       (INST_TYPE [alpha |-> ``:256``]
         send_call_value_preserves_storage_well_formed_on) >>
     disch_then irule >>
     qpat_assum `storage_well_formed_on _ (initial_state _ []) _`
       (fn th => irule (iffRL (MATCH_MP storage_well_formed_on_backends
         (Q.prove (`(initial_state am [FEMPTY] with
             <|outcomes := SOME os; requests := []; gas_obs := gs|>).accounts =
               (initial_state am []).accounts /\
           (initial_state am [FEMPTY] with
             <|outcomes := SOME os; requests := []; gas_obs := gs|>).tStorage =
               (initial_state am []).tStorage`, simp[initial_state_def])))) >>
         ACCEPT_TAC th)) >>
  `scope_well_typed env` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `state_well_typed s2 /\ accounts_well_typed s2.accounts /\
   !H. valid_horizon cx (initial_state am []) H s2.storage_trace ==>
     storage_well_formed_on cx s2 (FST H)` suffices_by
    (strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`es = s2 with scopes := [env]`, `s1.immutables = am.immutables`,
        `s2.immutables = s1.immutables`, `scope_well_typed env`,
        `state_well_typed s2`, `accounts_well_typed s2.accounts`,
        `!H. valid_horizon cx (initial_state am []) H s2.storage_trace ==>
           storage_well_formed_on cx s2 (FST H)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 7 strip_tac >>
     qpat_x_assum `es = _` SUBST_ALL_TAC >>
     conj_tac >- simp[] >>
     conj_tac
     >- (qpat_assum `state_well_typed s2`
           (mp_tac o REWRITE_RULE [state_well_typed_def]) >>
         simp[state_well_typed_def]) >>
     conj_tac >- simp[] >>
     qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx (initial_state am []) H s2.storage_trace` by fs[] >>
     `storage_well_formed_on cx s2 (FST H)` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (irule o SPEC_ALL) >>
        first_assum ACCEPT_TAC) >>
     `storage_well_formed_on cx (s2 with scopes := [env]) (FST H) <=>
      storage_well_formed_on cx s2 (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >>
     first_assum (fn th => PURE_REWRITE_TAC [th] >> first_assum ACCEPT_TAC)) >>
  drule lookup_function_External_cases >> strip_tac
  >- (`ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
      `module_allocated am.layouts tx.target NONE tops` by
        (drule check_contract_main_module_allocated >> simp[]) >>
      `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx s1.immutables` by
        fs[Abbr `cx`, checked_contract_runtime_ready_def] >>
      drule_all (Q.INST [`mods` |-> `[(NONE,tops)]`, `ts` |-> `tops`,
        `src` |-> `NONE`] checked_external_suffix_static) >>
      disch_then (qspec_then `LENGTH dflts - (LENGTH args - LENGTH tx.args)`
        strip_assume_tac) >>
      drule_all (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`,
        `st` |-> `s1`] checked_external_empty_frame_ready) >> strip_tac >>
      drule_all eval_external_defaults_type_sound >> strip_tac >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `H` >>
      simp_tac std_ss [valid_horizon_def] >> strip_tac >>
      `storage_well_formed_on cx s1 (FST H)` by
        (qpat_assum `storage_well_formed_on _ (initial_state _ []) _` mp_tac >>
         qpat_assum `!regions. storage_well_formed_on cx (initial_state am []) regions ==>
                        storage_well_formed_on cx s1 regions` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
      irule eval_external_defaults_storage_well_formed_on >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`artifact_env art [(NONE,tops)] NONE`,
        `DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts`,
        `INL dflt_vs`, `s1`] >>
      pure_rewrite_tac [vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
      rpt conj_tac >> simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  `dflts = []` by (drule external_getter_defaults >> simp[]) >>
  `s2 = s1` by
    (qpat_assum `eval_external_defaults _ _ _ = _` mp_tac >>
     qpat_assum `dflts = []` (fn th => simp_tac (srw_ss()) [th])) >>
  qpat_x_assum `s2 = s1` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp_tac std_ss [valid_horizon_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `storage_well_formed_on _ (initial_state _ []) _` mp_tac >>
  qpat_assum `!regions. storage_well_formed_on cx (initial_state am []) regions ==>
                 storage_well_formed_on cx s1 regions` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Theorem external_source_body_substitution_nr:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  external_entry_bound tops am tx os gs mut args dflts es0 /\
  lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
    nr (is_view_mut mut) es0 = (INL (),es_lock) ==>
  !gx. eval_stmts
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (subst_consts_stmts (module_consts_env tops []) fbody)
    (es_lock with gas_obs := gx) =
  eval_stmts
    (initial_evaluation_context am.sources am.layouts tx NONE)
    fbody (es_lock with gas_obs := gx)
Proof
  strip_tac >> drule_all external_entry_bound_source_frame >> strip_tac >>
  drule external_body_lock_frame >> strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = (exts,tail)` >> PairCases_on `tail` >>
  drule_all lower_vyper_runtime_unit_consts_guard >> strip_tac >>
  drule_all external_lookup_body_typing_canonical >>
  disch_then (qx_choosel_then [`art`, `env_t`, `env'`] strip_assume_tac) >>
  `env_t.event_fields = art.cta_event_fields` by
    fs[vyperTypeEventLookupTheory.function_entry_env_event_fields] >>
  qpat_x_assum `env_t = function_entry_env _ _ _ _ _` kall_tac >>
  drule source_typing_ok_consts_ready >> strip_tac >> gvs[] >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` by
    fs[source_deployment_rel_def] >>
  mp_tac (Q.INST
    [`cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
     `mods` |-> `[(NONE,tops)]`, `artifact` |-> `art`,
     `imms` |-> `account_immutables am tx.target`,
     `sc` |-> `[env]`, `current_src` |-> `NONE`]
    checked_module_consts_subst_context) >>
  impl_tac >- simp[initial_evaluation_context_def] >> strip_tac >>
  `const_subst_context roots
     (initial_evaluation_context am.sources am.layouts tx NONE)
     env_t (module_consts_env tops []) [(NONE,tops)] art` by
    (irule const_subst_context_static >> goal_assum (drule_at Any) >>
     simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
  gen_tac >> irule const_subst_eval_stmts >>
  goal_assum (drule_at Any) >> qexists_tac `ret` >>
  fs[const_cells_agree_def, initial_state_def]
QED

Theorem external_source_body_substitution:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
       <| outcomes := SOME os; requests := [] |>) = (INL (),es0) ==>
  !gx. eval_stmts
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (subst_consts_stmts (module_consts_env tops []) fbody)
    (es0 with gas_obs := gx) =
  eval_stmts
    (initial_evaluation_context am.sources am.layouts tx NONE)
    fbody (es0 with gas_obs := gx)
Proof
  strip_tac >>
  `lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
     F (is_view_mut mut) es0 = (INL (),es0)` by
    simp[lock_if_nr_def, vyperStateTheory.return_def] >>
  drule_all external_entry_bound_no_defaults >>
  disch_then (qspec_then `es0.gas_obs` assume_tac) >>
  `es0 with gas_obs := es0.gas_obs = es0` by
    simp[evaluation_state_component_equality] >>
  qpat_x_assum `es0 with gas_obs := _ = es0` (fn th =>
    qpat_x_assum `external_entry_bound _ _ _ _ _ _ _ _ _`
      (assume_tac o REWRITE_RULE [th])) >>
  drule_all external_source_body_substitution_nr >> simp[]
QED
