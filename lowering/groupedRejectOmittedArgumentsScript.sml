(* Model the omitted default expressions from the checked call state. *)
Theory groupedRejectOmittedArguments
Ancestors
  e2eDefs vyperLoweringCorrect ptrDiscipline loweringShapeProps compileVyper fragGasOriginPtr
  publicGetterProps vyperTypeContractContext vyperTypeContract list fragExec pred_set venomInst
  venomState bodyFullShadowBodyInvLowering externalBodyWidths allocLimitsProps
  runtimeDefaultCompile constSubstStmtsPreserve vyperTypeCallStackSoundness
  callRejectMemory[ignore_grammar] bodyPtrDefs groupedDefaultSyntax groupedKeywordDecode
  contextRawReachable selectedAcceptedFold abiDecoderCoherence compileEnv vyperContext
  entryStateRel vyperCompiler fragFuel finite_map rich_list words groupedKeywordInitialize
  groupedDefaultPre groupedDefaultOutcome groupedDefaultHorizon vyperStorageFootprint
  vyperInterpreter[qualified,ignore_grammar] vyperState[qualified,ignore_grammar]
  constSubst[qualified,ignore_grammar] pair loweringBudgetFrameOracleTransport arithmetic
  relation vyperAST groupedRejectCutRegistration groupedRejectModelFrame
Libs
  groupedRejectSlotsLib

val _ = Parse.hide "tops";

Triviality row22_model_alloc_limits:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  MEM (mut,nr,rr,name,args,ds,ret,fbody) (FST (classify_functions tops)) /\
  set_external_package_target rp.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,name,args,ds,ret,fbody)) =
    (lbl,ce,pos,mc,pay,nr,key,ut,iv,fbody,rt) ==>
  alloc_limits_exprs (ce with ce_vars := FEMPTY) ds
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fn_allocs_ok tops (mut,nr,rr,name,args,ds,ret,fbody)` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >> fs[] >>
     irule lower_vyper_runtime_unit_allocs_ok >> metis_tac[]) >>
  qabbrev_tac `c = build_compile_env tops Internal mut name args ret fbody F` >>
  `alloc_limits_exprs c ds` by fs[fn_allocs_ok_def, GSYM markerTheory.Abbrev_def] >>
  `alloc_limits_exprs (ce with ce_vars := FEMPTY) = alloc_limits_exprs c` suffices_by simp[] >>
  irule (cj 4 (UNDISCH (SPEC_ALL alloc_limits_frame)) |> DISCH_ALL) >>
  qabbrev_tac `ext = build_compile_env tops External mut name args ret fbody T` >>
  `(ce with ce_vars := FEMPTY).ce_struct_fields = ext.ce_struct_fields /\
   (ce with ce_vars := FEMPTY).ce_func_return_type = ext.ce_func_return_type /\
   (ce with ce_vars := FEMPTY).ce_modules = ext.ce_modules /\
   (ce with ce_vars := FEMPTY).ce_var_type = ext.ce_var_type /\
   (ce with ce_vars := FEMPTY).ce_hashmap_info = ext.ce_hashmap_info /\
   (ce with ce_vars := FEMPTY).ce_module_var_type = ext.ce_module_var_type /\
   (ce with ce_vars := FEMPTY).ce_module_vars = ext.ce_module_vars` by
    (Cases_on `ret = NoneT` >>
     gvs[package_external_fn_def,set_external_package_target_def,
        update_cenv_nonreentrant_def,update_cenv_ret_abi_def,GSYM markerTheory.Abbrev_def]) >>
  simp[] >> simp[Abbr `ext`, Abbr `c`, build_compile_env_def] >>
  rpt (pairarg_tac >> simp[])
QED

Triviality row22_model_default_annotation:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  well_typed_expr (artifact_env art [(NONE,tops)] NONE) e ==>
  expr_type (subst_consts_expr (module_consts_env tops []) e) = expr_type e
Proof
  strip_tac >> Cases_on `e` >>
  simp[constSubstTheory.subst_consts_expr_def, vyperASTTheory.expr_type_def] >>
  PairCases_on `p` >> Cases_on `p0` >>
  simp[constSubstTheory.subst_consts_expr_def, vyperASTTheory.expr_type_def] >>
  Cases_on `ALOOKUP (module_consts_env tops []) p1` >>
  gvs[constSubstTheory.subst_consts_expr_def, vyperASTTheory.expr_type_def] >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all constSubstCorrectTheory.checked_module_consts_env_replacement_annotation >>
  strip_tac >>
  `FLOOKUP art.cta_bare_globals (NONE,p1) = SOME ty` by
    (drule vyperTypeContractStaticMapsTheory.check_contract_nonsig_maps >> strip_tac >> simp[] >>
     irule vyperTypeContractStaticMapsTheory.build_contract_type_artifact_bare_globals_complete >>
     metis_tac[vyperTypeContractStaticMapsTheory.check_contract_runtime_namespaces]) >>
  imp_res_tac vyperTypeContractStaticMapsTheory.check_contract_bare_global_toplevel_vtype >>
  fs[vyperTypeSystemTheory.well_typed_expr_def,vyperTypeSystemTheory.vtype_annotation_ok_def,
     artifact_env_def]
QED

Triviality row22_model_default_syntax:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  MEM (mut,nr,rr,name,args,ds,ret,fbody) (FST (classify_functions tops)) /\
  cx = initial_evaluation_context am.sources am.layouts (tx with function_name := name) NONE ==>
  LENGTH ds <= LENGTH args /\
  MAP expr_type ds = MAP SND (DROP (LENGTH args - LENGTH ds) args) /\
  EVERY (runtime_constant_expr [(NONE,tops)]) ds /\
  well_typed_exprs (artifact_env art [(NONE,tops)] NONE) ds /\
  (!e. MEM e ds ==> ~supported_expr_exists (const_name_root cx) e)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule loweringShapePropsTheory.classify_functions_external_source >> strip_tac >>
  fs[constSubstTheory.subst_consts_fn_def] >-
    (drule_all grouped_checked_default_syntax >> strip_tac >>
     `MAP expr_type (subst_consts_exprs (module_consts_env tops []) rawdefaults) =
       MAP expr_type rawdefaults` by
       (simp[NoAsms, constSubstCorrectTheory.subst_consts_exprs_map, MAP_MAP_o] >>
        irule MAP_CONG >> simp[] >>
        metis_tac[row22_model_default_annotation, constSubstCorrectTheory.frame_well_typed_exprs_member]) >>
     simp[] >> simp[constSubstCorrectTheory.subst_consts_exprs_map, MEM_MAP, PULL_EXISTS] >>
     rpt strip_tac >>
     rename1 `MEM e rawdefaults` >>
     `cx_tops (initial_evaluation_context am.sources am.layouts
         (tx with function_name := name) NONE) = tops` by
       fs[gasContextTheory.cx_tops_def,vyperContextTheory.get_module_code_def,
          vyperInterpreterTheory.initial_evaluation_context_def,source_deployment_rel_def] >>
     qpat_assum `source_typing_ok tops am tx`
       (strip_assume_tac o REWRITE_RULE [e2eDefsTheory.source_typing_ok_def]) >>
     drule_all checked_const_substitution_const_name_free >>
     disch_then (qspec_then `[Expr e]` mp_tac) >>
     qpat_x_assum `supported_expr_exists (const_name_root _) _` mp_tac >>
     simp[constSubstTheory.subst_consts_stmt_def,
          supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
          GSYM exprSimHypsDefsTheory.const_name_root_mods_singleton]) >>
  drule public_getter_defaults >>
  simp[constSubstCorrectTheory.subst_consts_exprs_map,
       constSubstCorrectTheory.frame_well_typed_exprs_every]
QED

Triviality row22_model_context:
  source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  cx = initial_evaluation_context am.sources am.layouts (tx with function_name := name) NONE /\
  env = artifact_env art [(NONE,tops)] NONE ==>
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  get_tenv cx = type_env tops /\ cx_tops cx = tops /\ env.type_defs = get_tenv cx /\
  call_evaluation_safe cx [] /\
  (!e. well_typed_expr env e ==> byte_widths_expr e)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `source_deployment_rel tops am (tx with function_name := name)` by
    fs[source_deployment_rel_def,layouts_agree_def] >>
  drule source_deployment_context >> strip_tac >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` by fs[source_deployment_rel_def] >>
  `cx_tops cx = tops` by fs[gasContextTheory.cx_tops_def] >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
   cx.txn.target = tx.target /\ ~cx.in_deploy /\ (cx with stk := [(NONE,name)]) = cx` by
    fs[vyperInterpreterTheory.initial_evaluation_context_def] >>
  `call_evaluation_safe cx []` by
    (mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `calls` |-> `[]`,
       `owner` |-> `(NONE,name)`, `layouts` |-> `am.layouts`]
       (SPEC_ALL checked_contract_call_evaluation_safe_singleton)) >>
     simp[calls_follow_call_graph_def]) >>
  `!src id vt. FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME vt ==>
       well_formed_vtype (type_env_all_modules [(NONE,tops)]) vt` by
    (drule_at (Pat `check_contract _ _ _ _ = _`)
       vyperTypeContractStaticMapsTheory.check_contract_toplevel_vtypes_consistent_initial >>
     disch_then (qspecl_then [`tx`,`am.sources`] mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  `env.type_defs = get_tenv (initial_evaluation_context am.sources am.layouts
      (tx with function_name := name) NONE)` by
    simp[artifact_env_def,GSYM e2eProducersTheory.type_env_all_modules_single] >>
  simp[] >> rpt strip_tac >> irule well_typed_expr_byte_widths >>
  goal_assum (drule_at (Pat `well_typed_expr _ _`)) >>
  simp[artifact_env_def] >> first_assum ACCEPT_TAC
QED

Triviality row22_model_spec_annotations:
  LENGTH ds <= LENGTH args /\
  MAP expr_type ds = MAP SND (DROP (LENGTH args - LENGTH ds) args) /\
  MAP (\(n:string,_:operand,ty,e). (n,ty,e)) vars =
    MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP (LENGTH args - LENGTH ds) args,ds)) ==>
  !n dst ty e. MEM (n,dst,ty,e) vars ==>
     MEM (n,ty) args /\ MEM e ds /\ expr_type e = ty
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  `MEM (n,ty,e) (MAP (\(n,_,ty,e). (n,ty,e)) vars)` by
    (simp[MEM_MAP] >> goal_assum (drule_at (Pat `MEM _ vars`)) >> simp[]) >>
  qpat_assum `MAP _ vars = _` (fn th => pop_assum (mp_tac o REWRITE_RULE [th])) >>
  `LENGTH (DROP (LENGTH args - LENGTH ds) args) = LENGTH ds` by simp[LENGTH_DROP] >>
  simp[MEM_MAP, EXISTS_PROD, MEM_ZIP] >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  conj_tac >- metis_tac[MEM_EL, MEM_DROP] >>
  conj_tac >- metis_tac[MEM_EL] >>
  qpat_assum `MAP expr_type ds = _` (mp_tac o Q.AP_TERM `EL j`) >> simp[EL_MAP] >>
  qpat_assum `(n,ty) = EL j _` (fn th => simp[NoAsms, SYM th])
QED

Triviality row22_model_slot_inputs:
  LIST_REL (^row22_kw_meta ce (type_env tops)) vspec slots /\
  (!n dst ty e. MEM (n,dst,ty,e) vspec ==> MEM (n,ty) args /\ MEM e ds /\ expr_type e = ty) /\
  EVERY (runtime_constant_expr [(NONE,tops)]) ds /\
  well_typed_exprs env ds /\ alloc_limits_exprs (ce with ce_vars := FEMPTY) ds /\
  (!e. MEM e ds ==> ~supported_expr_exists (const_name_root cx) e) /\
  (!e. well_typed_expr env e ==> byte_widths_expr e) /\
  get_tenv cx = type_env tops /\ cx_tops cx = tops /\ call_evaluation_safe cx [] /\
  fn_allocs_ok tops (mut,(nr:bool),(rr:bool),(name:string),args,ds,ret,fbody) /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ==>
  LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
    dst = Var p /\ runtime_constant_expr [(NONE,tops)] e /\ expr_type e = ty /\
    (!es'. expr_sim_inv (ce with ce_vars := FEMPTY) cx env es' ==>
      expr_body_pre (ce with ce_vars := FEMPTY) cx env e es') /\
    lower_value compile_expr (ce with ce_vars := FEMPTY) ty e = lower_value compile_expr ce ty e /\
    lower_value compile_expr (gas_shadow_env T ce with ce_vars := FEMPTY) ty
        (gas_shadow_expr e) =
      lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256)) vspec slots
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `LIST_REL _ vspec slots` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >> qx_gen_tac `j` >> strip_tac >>
  `j < LENGTH slots` by simp[] >>
  Cases_on `EL j vspec` >> PairCases_on `r` >> Cases_on `EL j slots` >> PairCases_on `r` >>
  rename1 `EL j vspec = (n,dst,ty,e)` >> rename1 `EL j slots = (_,_,_,tv:type_value)` >>
  `MEM (n,dst,ty,e) vspec` by metis_tac[MEM_EL] >>
  `MEM (n,ty) args /\ MEM e ds /\ expr_type e = ty` by metis_tac[] >>
  `well_typed_expr env e` by metis_tac[exprSimSourceTheory.well_typed_exprs_member] >>
  qpat_assum `!i. i < LENGTH vspec ==> _` (qspec_then `j` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (fn th =>
    qpat_assum `EL j vspec = _` (fn hv =>
    qpat_assum `EL j slots = _` (fn hs =>
      strip_assume_tac (SIMP_RULE (srw_ss()) [hv,hs] th)))) >>
  drule abi_decoder_coherent_header >>
  disch_then (strip_assume_tac o REWRITE_RULE [abi_decoder_header_def]) >>
  `runtime_constant_expr [(NONE,tops)] e` by fs[EVERY_MEM] >>
  `type_memory_size tv < 2 ** 64` by
    metis_tac[registrationSizeAdmissibilityTheory.registration_parameter_memory_limit] >>
  `type_memory_size tv + 64 < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
  drule runtime_default_lower_value_vars_frame >>
  impl_tac >- metis_tac[cj 1 well_typed_expr_builtin_args_length] >> simp[] >>
  strip_tac >> simp[] >> rpt strip_tac >> irule runtime_constant_expr_body_pre >>
  simp[] >> metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]
QED

Triviality row22_model_no_sha:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  MEM (mut,nr,rr,name,args,ds,ret,fbody) (FST (classify_functions tops)) /\
  MAP (\(_:string,_:operand,_:type,e). e) (DROP k vars) = DROP k ds ==>
  no_sha256_exprs (MAP (\(_,_,_,e). e) (DROP k vars))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY external_defaults_no_sha256 (FST (classify_functions tops))` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
     simp[Once lower_vyper_runtime_unit_def] >> rw[] >> fs[EXISTS_MEM,EVERY_MEM] >> metis_tac[]) >>
  `no_sha256_exprs ds` by
    (fs[EVERY_MEM] >> first_x_assum drule >> simp[external_defaults_no_sha256_def]) >>
  `!es j. no_sha256_exprs es ==> no_sha256_exprs (DROP j es)` suffices_by simp[] >>
  Induct >> simp[constSubstTheory.no_sha256_expr_def] >>
  rpt gen_tac >> Cases_on `j` >> simp[constSubstTheory.no_sha256_expr_def]
QED

Triviality row22_model_package:
  package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,ds,ret,fbody) = ExternalDefaults common entries specs off ==>
  (common.ec_payable <=> mut = Payable) /\
  ?lbl pos mc pay key ut iv rt.
    set_external_package_target rp.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,nr,rr,name,args,ds,ret,fbody)) =
      (lbl,common.ec_env,pos,mc,pay,nr,key,ut,iv,fbody,rt)
Proof
  Cases_on `ret = NoneT` >>
  simp[package_external_group_def,package_external_fn_def,set_external_package_target_def, LET_THM] >>
  simp[AllCaseEqs(), GSYM CONJ_ASSOC] >> strip_tac >> gvs[]
QED

Theorem row22_omitted_model_inputs:
  lower_vyper_runtime_unit tops rp = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\ calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  MEM (mut,nr,rr,name,args,ds,ret,fbody) (FST (classify_functions tops)) /\
  package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,ds,ret,fbody) = ExternalDefaults common entries specs off /\
  (common.ec_payable \/ vs.vs_call_ctx.cc_callvalue = 0w) /\
  ce = common.ec_env /\ ctx = unit.cu_context /\
  lookup_function "__entry" ctx.ctx_functions = SOME fn /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit /\ gas_shadow_unit unit shadow_unit /\
  lookup_function "__entry" shadow_unit.cu_context.ctx_functions = SOME shfn /\
  fn_inst_ids_distinct fn /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  compile_create_kwarg_allocas ce specs alloc_start = (vars,alloc_end) /\
  specs = MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP (LENGTH args - LENGTH ds) args,ds)) /\
  MAP (\(_,_,_,e). e) (DROP k vars) = DROP k ds /\
  LIST_REL (^row22_kw_meta ce (type_env tops)) (DROP k vars) slots /\
  EVERY (^row22_kw_alloc sa u G tn) slots /\
  LIST_REL (\(aid,p,base,tv) v. ^row22_kw_initialized sa u G tn (aid,p,base,tv,v))
    supplied vals /\
  selected_registration_frame vs entry_taint u tn /\
  selected_registration_resources ctx fn site 0 sa u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    unit_alloca_budget ctx <= w2n vs.vs_initial_fmp /\ w2n vs.vs_initial_fmp < 2 ** 254) /\
  gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) [] (OK u,G,tn) ==> 
  ?art es cx env s.
    cx = initial_evaluation_context am.sources am.layouts (tx with function_name := name) NONE /\
    env = artifact_env art [(NONE,tops)] NONE /\
    s = u with vs_outcomes := [] /\
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
    cx_tops cx = tops /\ env.type_defs = get_tenv cx /\
    EVERY (runtime_constant_expr [(NONE,tops)]) (MAP (\(_,_,_,e). e) (DROP k vars)) /\
    no_sha256_exprs (MAP (\(_,_,_,e). e) (DROP k vars)) /\
    LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
      dst = Var p /\ runtime_constant_expr [(NONE,tops)] e /\ expr_type e = ty /\
      (!es'. expr_sim_inv (ce with ce_vars := FEMPTY) cx env es' ==>
        expr_body_pre (ce with ce_vars := FEMPTY) cx env e es') /\
      lower_value compile_expr (ce with ce_vars := FEMPTY) ty e = lower_value compile_expr ce ty e /\
      lower_value compile_expr (gas_shadow_env T ce with ce_vars := FEMPTY) ty
        (gas_shadow_expr e) =
        lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256))
      (DROP k vars) slots /\
    EVERY (^row22_kw_alloc sa s G tn) slots /\
    EVERY (^row22_kw_initialized sa s G tn)
      (MAP (\((aid,p,base,tv),v). (aid,p,base,tv,v)) (ZIP (supplied,vals))) /\
    body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\
    shadow_body_inv tops ctx shadow_unit.cu_context /\
    gas_shadow_context ctx shadow_unit.cu_context /\ ctx_inst_ids_distinct ctx /\
    MEM fn ctx.ctx_functions /\ MEM shfn shadow_unit.cu_context.ctx_functions /\
    ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\ ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
    (!H. dead_lo_ok H (cx_dead H cx) 0 (ce with ce_vars := FEMPTY) cx) /\
    (!H. valid_horizon cx (initial_state am []) H es.storage_trace ==>
      stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (cx_dead H cx) 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s) /\
    storage_trace_domain cx (initial_state am []) es.storage_trace /\
    expr_sim_inv (ce with ce_vars := FEMPTY) cx env es /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    alloca_history fn s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!f inst w. frag_reachable ctx fn s f inst w ==> dalloca_fmp_headroom inst w) /\
    ~s.vs_halted /\ at_point sa s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ce = _` (assume_tac o SYM) >>
  qpat_x_assum `ctx = _` SUBST_ALL_TAC >>
  drule row22_model_package >> strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts (tx with function_name := name) NONE` >>
  `cx = initial_evaluation_context am.sources am.layouts (tx with function_name := name) NONE` by simp[Abbr `cx`] >>
  mp_tac (SPEC_ALL row22_model_source) >>
  impl_tac >-
    (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`art`,`es`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `common.ec_env = ce` (assume_tac o SYM) >>
  qexistsl_tac [`art`, `es`, `cx`, `artifact_env art [(NONE,tops)] NONE`,
    `u with vs_outcomes := []`] >>
  simp[NoAsms] >>
  qabbrev_tac `kept = MAP (\((aid,p,base,tv),v). (aid,p,base,tv,v)) (ZIP (supplied,vals))` >>
  drule_all row22_model_default_syntax >> strip_tac >>
  mp_tac (Q.INST [`env` |-> `artifact_env art [(NONE,tops)] NONE`] (SPEC_ALL row22_model_context)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  drule compile_create_kwarg_allocas_preserves_specs >>
  qpat_assum `specs = _` (fn th => disch_then (assume_tac o REWRITE_RULE [th])) >>
  mp_tac (SPEC_ALL row22_model_spec_annotations) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `!n dst ty e. MEM (n,dst,ty,e) (DROP k vars) ==>
      MEM (n,ty) args /\ MEM e ds /\ expr_type e = ty` by
    (rpt gen_tac >> disch_then (assume_tac o MATCH_MP MEM_DROP_IMP) >>
     qpat_assum `!n dst ty e. MEM (n,dst,ty,e) vars ==> _` (drule_then ACCEPT_TAC)) >>
  drule_all row22_model_alloc_limits >> strip_tac >>
  `fn_allocs_ok tops (mut,nr,rr,name,args,ds,ret,fbody)` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >> fs[] >>
     irule lower_vyper_runtime_unit_allocs_ok >> metis_tac[]) >>
  drule source_typing_ok_type_def_keys_distinct >> strip_tac >>
  mp_tac (Q.INST [`vspec` |-> `DROP k vars`, `env` |-> `artifact_env art [(NONE,tops)] NONE`]
    (SPEC_ALL row22_model_slot_inputs)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (SPEC_ALL row22_model_no_sha) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `EVERY (runtime_constant_expr [(NONE,tops)]) (MAP (\(_,_,_,e). e) (DROP k vars))` by
    (qpat_assum `MAP _ (DROP k vars) = _` SUBST1_TAC >>
     irule EVERY_DROP >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `ce = _` kall_tac >>
  `unit_alloca_budget unit.cu_context < dimword (:256) /\ ctx_inst_ids_distinct unit.cu_context` by
    metis_tac[lower_vyper_runtime_unit_context_entry,lowering_context_ok_alloca_budget,
              lowering_context_ok_static_integrity] >>
  `MEM fn unit.cu_context.ctx_functions /\ MEM shfn shadow_unit.cu_context.ctx_functions` by
    metis_tac[lookup_function_MEM] >>
  `shadow_body_inv tops unit.cu_context shadow_unit.cu_context` by
    (irule runtime_shadow_body_inv >>
     conj_tac >- (drule source_typing_ok_vtype_keys_distinct >> strip_tac >> first_assum ACCEPT_TAC) >>
     simp[] >> qexists_tac `rp` >> asm_rewrite_tac[]) >>
  drule_all row22_model_initial_rel >> disch_then (qspec_then `name` strip_assume_tac) >>
  `cx.txn = tx with function_name := name` by
    simp[vyperInterpreterTheory.initial_evaluation_context_def] >>
  `(ctx_has_dalloca unit.cu_context ==> unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254)` by metis_tac[] >>
  mp_tac (Q.INST [`tx` |-> `tx with function_name := name`,
    `ctx` |-> `unit.cu_context`, `J` |-> `G`, `tz` |-> `tn`,
    `ce` |-> `ce with ce_vars := FEMPTY`,
    `os0` |-> `vs.vs_outcomes`, `os1` |-> `u.vs_outcomes`]
    (SPEC_ALL row22_model_frame)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.INST [`cut` |-> `u`, `marks` |-> `[]`]
    (SPEC_ALL row22_real_cut_empty_oracle_headroom)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >>
  qpat_x_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[selected_registration_resources_def]) >>
  `EVERY (^row22_kw_alloc sa (u with vs_outcomes := []) G tn) slots` by
    (qpat_assum `EVERY _ slots` mp_tac >>
     simp[NoAsms,ptr_covers_def,lookup_var_outcomes_update]) >>
  `EVERY (^row22_kw_initialized sa (u with vs_outcomes := []) G tn) kept` by
    (qpat_assum `LIST_REL _ supplied vals` mp_tac >>
     simp[NoAsms,Abbr `kept`,LIST_REL_EVERY_ZIP,EVERY_MAP,EVERY_MEM,FORALL_PROD,
          ptr_covers_def,lookup_var_outcomes_update] >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  qpat_assum `gas_shadow_unit _ _`
    (strip_assume_tac o REWRITE_RULE[gasShadowUnitTheory.gas_shadow_unit_def]) >>
  qpat_x_assum `cx = initial_evaluation_context _ _ _ _` SUBST_ALL_TAC >>
  simp[at_point_def, dead_lo_ok_def, storage_trace_domain_def,
       storage_trace_horizon_def, storage_trace_regions_def, storage_trace_locks_def,
       grouped_default_empty_regions_horizon, ptr_predicates_outcomes_update] >>
  rpt conj_tac >> first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_assum ACCEPT_TAC >>
  fs[valid_horizon_def] >>
  qpat_assum `!regions. storage_well_formed_on _ _ regions ==>
                        storage_well_formed_on _ _ regions` mp_tac >>
  qpat_assum `storage_well_formed_on _ (initial_state _ []) _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED

Theorem row22_omitted_seed_path_if_no_exempt:
  compile_init_kwargs ce vars off 0 hi sa = ((),sb) /\
  compile_init_kwargs (gas_shadow_env T ce)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
    off 0 hi sha = ((),shb) /\
  fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha /\
  LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
    dst = Var p /\ runtime_constant_expr [(NONE,src_tops)] e /\ expr_type e = ty /\
    (!es'. expr_sim_inv (ce with ce_vars := FEMPTY) cx env es' ==>
      expr_body_pre (ce with ce_vars := FEMPTY) cx env e es') /\
    lower_value compile_expr (ce with ce_vars := FEMPTY) ty e =
      lower_value compile_expr ce ty e /\
    lower_value compile_expr (gas_shadow_env T ce with ce_vars := FEMPTY) ty
        (gas_shadow_expr e) =
      lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes ce ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256)) vars slots /\
  EVERY (^row22_kw_alloc sa s G tn) slots /\
  EVERY (^row22_kw_initialized sa s G tn) kept /\
  ALL_DISTINCT (MAP FST slots ++ MAP FST kept) /\
  body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\ shadow_body_inv tops ctx shadow_ctx /\
  env.type_defs = get_tenv cx /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function fn shfn /\ MEM fn ctx.ctx_functions /\ MEM shfn shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct fn /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) 0 (ce with ce_vars := FEMPTY) cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s) /\
  expr_sim_inv (ce with ce_vars := FEMPTY) cx env es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  alloca_history fn s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f inst u. frag_reachable ctx fn s f inst u ==> dalloca_fmp_headroom inst u) /\
  ~s.vs_halted /\ at_point sa s /\
  check_contract F layouts addr [(NONE,src_tops)] = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,src_tops)] /\
  no_sha256_exprs (MAP (\(_,_,_,e). e) vars) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!st ee err. eval_exprs cx (MAP (\(_,_,_,e). e) vars) st = (INR (Error err),ee) ==>
    ~unspecified_behaviour_exempt (cx_tops cx) err) ==>
  ?D explicit marks r J tz.
    gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (s,G,tn) marks (r,J,tz) /\
    (!w. r = OK w ==> at_point sb w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ds = MAP (\(_,_,_,e). e) vars` >>
  `EVERY (runtime_constant_expr [(NONE,src_tops)]) ds` by
    (simp[Abbr `ds`, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
     simp[FORALL_PROD] >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP >>
     disch_then (qx_choose_then `slot` strip_assume_tac) >>
     PairCases_on `slot` >> fs[]) >>
  `!gs. (SND (eval_exprs cx ds (es with gas_obs := gs))).storage_trace =
       es.storage_trace` by
    (gen_tac >> Cases_on `eval_exprs cx ds (es with gas_obs := gs)` >>
     drule_all grouped_checked_default_source_frame >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `gas_shadow_env T (ce with ce_vars := FEMPTY) =
     (gas_shadow_env T ce) with ce_vars := FEMPTY` by
    rw[gasShadowCompileBaseTheory.gas_shadow_env_def, compile_env_component_equality] >>
  pop_assum $ mk_asm "shadow_vars" >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,src_tops)]`, `PG` |-> `[]`]
    (SPEC_ALL grouped_omitted_initializers)) >>
  asm_x "shadow_vars" (pure_rewrite_tac o single) >>
  impl_tac >-
    (qpat_assum `at_point sa s` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (ds = _)`
    (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  strip_tac >> drule_all grouped_default_initializer_outcome >>
  disch_then (qx_choosel_then [`marks`,`res`,`ee`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac DISJ_CASES_TAC)))
  >- (qpat_x_assum `?r J tz. _` (qx_choosel_then [`r`,`J`,`tz`] assume_tac) >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
        fs[storage_trace_domain_def] >>
      first_x_assum (drule_then strip_assume_tac) >>
      goal_assum (drule_at Any) >> rw[at_point_def] >> fs[exit_result_def]) >>
  pop_assum (qx_choosel_then [`err`,`H`,`leaf`,`pg`,`J`,`tz`,`focus_state`] strip_assume_tac) >>
  qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]:bytes32 list` mp_tac) >>
  qpat_assum `res = INR _` (pure_rewrite_tac o single) >>
  qpat_assum `!st ee err. eval_exprs _ _ _ = _ ==> ~_`
    (fn th => disch_then (mp_tac o MATCH_MP (SPEC_ALL th))) >> simp[]
QED
