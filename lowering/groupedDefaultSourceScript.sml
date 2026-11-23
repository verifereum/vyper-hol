Theory groupedDefaultSource
Ancestors
  externalBodySupport e2eDefs vyperTypeExternalDefaults vyperTypeContractSoundness
  vyperTypeContract vyperTypeInitialState vyperTypeInvariants
  vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  vyperExternalEntryStorageFrame exprSimHypsDefs finite_map alist
  externalBodyFrame bodySim bodySimEntry compileEnv compileVyper vyperContext
  supportedProgramProps immutableLocationProps placeTypingBuildProps
  vyperTypeContractContext vyperTypeContractStaticMaps list
  bodySimStmtFacts entryStateRel entryDecodePlanProps bodyInvIntCallPinsProps
  bodyInvCodeProps bodyInvExecutionProps bodyInvMetadataProps bodyInvSplit compileUnit

Theorem grouped_default_empty_source_frame:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  outcomes_accounts_typed (SOME os) /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := SOME os; requests := []|>) =
    (INL (), es) ==>
  env_consistent (artifact_env art [(NONE,tops)] NONE) cx es /\
  state_well_typed es /\ accounts_well_typed es.accounts /\
  context_well_typed cx /\ functions_well_typed cx /\
  outcomes_accounts_typed es.outcomes /\ es.outcomes = SOME os /\
  es.immutables = am.immutables /\ es.scopes = [FEMPTY] /\
  es.gas_obs = [] /\ es.storage_trace = [] /\
  !regions. storage_well_formed_on cx (initial_state am []) regions ==>
    storage_well_formed_on cx es regions
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  drule_all external_source_context_typed >> strip_tac >>
  qpat_assum `send_call_value _ _ _ = _`
    (strip_assume_tac o
      SIMP_RULE (srw_ss()) [evaluation_state_component_equality, initial_state_def] o
      MATCH_MP external_send_call_value_frame) >>
  `accounts_well_typed es.accounts` by
    (irule send_call_value_accounts_well_typed_c53 >>
     goal_assum (drule_at Any) >>
     fs[machine_well_typed_def, initial_state_def]) >>
  `state_well_typed es` by
    (simp[state_well_typed_def, scope_well_typed_def] >>
     fs[machine_well_typed_def]) >>
  `checked_contract_runtime_ready art [(NONE,tops)] am tx` by
    metis_tac[optionTheory.SOME_11] >>
  `art' = art` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `art' = art` SUBST_ALL_TAC >>
  `es with scopes := [FEMPTY] = es` by simp[evaluation_state_component_equality] >>
  qpat_assum `checked_contract_runtime_ready art [(NONE,tops)] am tx`
    (strip_assume_tac o REWRITE_RULE [checked_contract_runtime_ready_def]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (mp_tac (Q.INST [`st` |-> `es`, `src` |-> `NONE:num option`,
       `am` |-> `am`, `tx` |-> `tx`, `art` |-> `art`,
       `mods` |-> `[(NONE,tops)]`, `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`]
       (SPEC_ALL checked_external_empty_frame_ready)) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule send_call_value_preserves_storage_well_formed_on >>
  qexistsl_tac [`mut`,`INL ()`,
    `initial_state am [FEMPTY] with <|outcomes := SOME os; requests := []|>`] >>
  asm_rewrite_tac[] >>
  mp_tac (Q.INST [`st'` |-> `initial_state am [FEMPTY] with <|outcomes := SOME os; requests := []|>`,
    `st` |-> `initial_state am []`, `regions` |-> `regions`,
    `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`]
    (SPEC_ALL storage_well_formed_on_backends)) >>
  simp[initial_state_def] >>
  qpat_assum `storage_well_formed_on _ (initial_state am []) regions` mp_tac >>
  simp[initial_state_def]
QED

Theorem grouped_default_empty_expr_sim:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,ce0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,fbody,rt) /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es) ==>
  expr_sim_inv (ce0 with ce_vars := FEMPTY) cx (artifact_env art [(NONE,tops)] NONE) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_default_empty_source_frame >> strip_tac >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  qabbrev_tac `ce = ce0 with ce_vars := FEMPTY` >>
  `ce with ce_vars := ce0.ce_vars = ce0` by simp[Abbr `ce`] >>
  drule_at (Pat `lower_vyper_runtime_unit _ _ = _`) external_package_body_inv >>
  disch_then (drule_all_then strip_assume_tac) >>
  drule_at (Pat `source_typing_ok _ _ _`) external_package_dec_metadata >>
  disch_then (drule_all_then assume_tac) >>
  drule_at (Pat `source_deployment_rel _ _ _`) external_package_method_id >>
  disch_then (drule_all_then assume_tac) >>
  `env_consistent (artifact_env art [(NONE,tops)] NONE)
     (initial_evaluation_context am.sources am.layouts tx NONE) es` by
    simp[GSYM markerTheory.Abbrev_def] >>
  qabbrev_tac `env_t = artifact_env art [(NONE,tops)] NONE` >>
  `env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
   env_t.bare_globals = art.cta_bare_globals /\
   env_t.fn_sigs = art.cta_fn_sigs /\ env_t.var_types = FEMPTY` by
    simp[Abbr `env_t`, artifact_env_def] >>
  drule_all external_package_global_maps >> strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `rpolicy` |-> `rpolicy`, `unit` |-> `unit`,
    `am` |-> `am`, `tx` |-> `tx`, `vs` |-> `vs`, `es0` |-> `es`,
    `env_t` |-> `env_t`, `target` |-> `rpolicy.rpol_target`,
    `rr` |-> `rr`, `mut` |-> `mut`, `nr` |-> `nr`, `dflts` |-> `dflts`,
    `fbody` |-> `fbody`, `args` |-> `args`, `ret` |-> `ret`, `lbl` |-> `lbl`,
    `cenv0` |-> `ce0`, `pos_args` |-> `pos_args`, `min_cds` |-> `min_cds`,
    `is_payable` |-> `is_payable`, `nkey` |-> `nkey`, `iv` |-> `iv`,
    `ut'` |-> `ut`, `rt` |-> `rt`, `cenv` |-> `ce`]
    (SPEC_ALL external_package_bare_globals)) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  `~cx.in_deploy` by simp[Abbr `cx`,initial_evaluation_context_def] >>
  qpat_assum `source_deployment_rel tops am tx`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [source_deployment_rel_def]) >>
  `!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops` by
    (gen_tac >> Cases_on `src` >>
     qpat_assum `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` (fn lookup =>
       simp[NoAsms, Abbr `cx`, get_module_code_def,
            initial_evaluation_context_def, lookup])) >>
  `!src ts. get_module_code cx src = SOME ts ==> src = NONE` by
    metis_tac[] >>
  `cenv_module_pins tops ce` by (drule intcall_args_body_inv_pins >> simp[]) >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_type_def_keys_distinct] >>
  `get_tenv cx = type_env tops` by
    (simp_tac (srw_ss()) [Abbr `cx`,get_tenv_def, initial_evaluation_context_def,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
     asm_simp_tac (srw_ss()) [type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]) >>
  qpat_assum `env_consistent env_t cx es`
    (strip_assume_tac o REWRITE_RULE [env_consistent_def,env_context_consistent_def]) >>
  qpat_assum `dec_cenv_agrees _ _`
    (strip_assume_tac o REWRITE_RULE [dec_cenv_agrees_def]) >>
  `popped_keys_indexed es.scopes` by simp[popped_keys_indexed_def] >>
  `body_inv tops unit.cu_context ce cx` by
    (qpat_assum `Abbrev (cx = _)`
      (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`tops`, `unit.cu_context`, `ce`, `cx`] body_inv_storage_var_types) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >>
  qpat_assum `Abbrev (cx = _)` (fn th =>
    let val cx_eq = REWRITE_RULE [markerTheory.Abbrev_def] th in
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [SYM cx_eq]) >> ASSUME_TAC cx_eq
    end) >>
  pure_rewrite_tac[expr_sim_inv_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`FLOOKUP env_t.var_types`] >- simp[]
  >~ [`FLOOKUP env_t.var_types`] >- simp[]
  >~ [`IS_SOME es.outcomes`] >- simp[]
  >~ [`FLOOKUP env_t.fn_sigs`]
  >- (rpt strip_tac >> irule external_signature_return >>
      qexistsl_tac [`cx`,`env_t.fn_sigs`,`tops`] >>
      `ce.ce_func_return_type = build_func_return_type tops` by
        (qpat_assum `body_inv tops _ ce _`
           (mp_tac o MATCH_MP contract_inv_return_types o MATCH_MP body_inv_contract) >>
         simp[compileUnitTheory.build_func_return_type_mods_singleton]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`ce.ce_flag_member_id`]
  >- (rpt strip_tac >> irule external_source_flag_member_id >>
      qexistsl_tac [`am`,`ls`,`tops`,`ts`,`tx`] >>
      qpat_assum `cx = _` (fn th => pure_rewrite_tac [SYM th]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`FLOOKUP ce.ce_struct_fields`]
  >- (rpt strip_tac >>
      drule_at (Pat `FLOOKUP ce.ce_struct_fields name = SOME fields`)
        external_package_struct_fields >>
      disch_then (drule_all_then mp_tac) >>
      qpat_assum `cx = _` (fn th => pure_rewrite_tac [SYM th]) >>
      simp[]) >>
  suspend "layout"
QED

Resume grouped_default_empty_expr_sim[layout]:
  drule body_inv_modules_aligned >> strip_tac >>
  drule_then strip_assume_tac body_inv_module_locations >>
  qpat_assum `body_inv tops _ ce cx`
    (assume_tac o MATCH_MP contract_inv_constructor o MATCH_MP body_inv_contract) >>
  qpat_assum `ce.ce_is_ctor <=> cx.in_deploy`
    (fn th => simp_tac bool_ss [bare_globals_layout_def, th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_x_assum `FLOOKUP ce.ce_module_vars _ = SOME (ImmutableLoc _)` mp_tac >>
      qpat_assum `ce.ce_module_vars = _` (fn th => pure_rewrite_tac [th]) >>
      disch_tac >>
      drule add_immutable_locations_cases >> strip_tac
      >- (drule add_module_var_locations_FLOOKUP >> simp[]) >>
      drule body_inv_main_code >> strip_tac >>
      qpat_assum `bare_globals_complete env_t.bare_globals cx`
        (mp_tac o REWRITE_RULE [bare_globals_complete_def]) >>
      disch_then (qspecl_then [`NONE`,`tops`,`vis`,`Immutable`,`name`,`ty`,`slot`] mp_tac) >>
      simp[])
  >- (rpt strip_tac >> drule_all body_inv_bare_global_type >> simp[]) >>
  rpt strip_tac >>
  `src = NONE /\ ce.ce_module_var_type (src,id1) = SOME ty1 /\
   ce.ce_module_var_type (src,id2) = SOME ty2` by
    metis_tac[body_inv_bare_global_type] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (qpat_assum `body_inv tops _ ce cx` (fn inv =>
       ACCEPT_TAC (MATCH_MP contract_inv_module_distinct_keys
         (CONJ (MATCH_MP body_inv_contract inv) (MATCH_MP body_inv_module inv))))) >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`tops`,`ce`,`cx`,`id1`,`id2`,`ty1`,`ty2`,
    `off1`,`off2`,`tv1`,`tv2`] cenv_module_pins_immutables_disjoint) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Finalise grouped_default_empty_expr_sim
