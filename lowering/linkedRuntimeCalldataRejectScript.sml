(* Rejection certificate for malformed calldata in a linked runtime unit. *)
Theory linkedRuntimeCalldataReject
Ancestors
  linkedCalldataMiss linkedLinearCalldataReject linkedFallbackAbsent
  linkedGroupedRejectSeed linkedGroupedShadowBodyInv linkedBodyConstantCells
  linkedGroupedDefaultSyntax linkedGroupedDefaultSource
  linkedConstAccessSubset linkedOwnedImmutableLocation supportedExprTraverse exprSimHypsDefs
  vyperSubscriptOverlap vyperTypeContractStaticMaps alist
  linkedContractInvProducer linkedEntryBodyTables linkedCallPremises
  sourceValueRejection externalBodySupport vyperTypeContractSoundness vyperTypeInvariants
  vyperInterpreter vyperTypeContract constSubstCorrect option
  groupedRejectSuppliedArguments groupedRejectSelection groupedEntryResources
  groupedRejectCutRegistration groupedRejectReplay groupedKeywordReject
  decoderOriginAllocationFrame groupedRejectCutAllocationProps bodyMemBopRestWordPath
  allocaHistory groupedEntryCommon linkedRegistrationPackageInputs
  rawReachableFmp o1PipelineCompose o1PassContract fragFuel memSafeRun
  lowerDloadPtrDalloca taintAgree venomInstProofs1 venomExecProofs
  linkedRawUnitShape runtimeUnitShapeMods dispatchedSignatureOriginMods
  dispatchedSignatureMemberMods linkedEntryCheckResources entryJointRevertExit
  callRejectMemory[qualified] loweringCalldataCorrect[qualified]
  bodySimFullMain[qualified] fragGasOriginPtr compileEnv vyperCompiler pred_set
  e2eModsDefs sourceUnitExecutionMods vyperLoweringCorrect loweringStateRelDefs
  compileUnit vyperCalldata fragGasPathMem fragGasPathPtr ptrSafeRun
  venomExecSemantics venomState venomInst finite_map list pair arithmetic
  groupedInternalLabels entryRejectCode loweringShapeDefs compileVyper ptrDiscipline
  groupedDispatchPath fragGasEmitCtrl moduleLoweringProps fragExec
  compileUnitPackageShape loweringShapeProps loweringShapeSource rich_list
  entryPtrSeamRegister selectedAcceptedFold allocaFrontierBound allocaFrontierRoom
  venomInstIdsProps venomMemDefs venomMemProps venomWf words
  vyperABIEntries defaultDispatchModsGetter dispatchedClassifierMods vyperReadOnlySyntax constSubstMods
  gasShadowModuleDefs gasShadowState gasShadow selectorCompilerProps moduleLowering
  requestCutOracleClip[qualified] bodyFullIfExpReach[qualified]
  deployBodyReachability[qualified] extCallOracle[qualified] fragGasPath contextCodegenRel[qualified]
Libs groupedRejectSlotsLib runtimeDefaultRejectSyntaxLib groupedRejectCutLib

val row22_kw_alloc = groupedRejectSlotsLib.row22_kw_alloc;
val row22_kw_initialized = groupedRejectSlotsLib.row22_kw_initialized;
val checked_default_expr = runtimeDefaultRejectSyntaxLib.checked_default_expr;
val row22_cut_facts = groupedRejectCutLib.row22_cut_facts;

Theorem lower_vyper_runtime_unit_reverts_mods:
  !mods exps rpolicy unit am tx vs.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    source_typing_ok_mods mods exps am tx /\
    source_deployment_rel_mods mods exps am tx /\
    calldata_dispatch_mods mods exps vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel_mods mods am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254)
    /\ (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable (vs with vs_outcomes := []) unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s)
    ==>
    ?func s G' tn' n.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) n (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>) n G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
                  (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                              vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `classify_functions_unit mods exps` >> PairCases_on `r` >>
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors)` >>
  Cases_on `EXISTS (external_has_defaults o SND) exts`
  >- suspend "grouped_rejection" >>
  qabbrev_tac `cd = vs.vs_call_ctx.cc_calldata` >>
  Cases_on `if LENGTH cd < 4 then NONE
    else FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys =
      cd_selector cd) (abi_deployed_signatures mods exps)`
  >- (
      `~list$EXISTS is_default_decl (main_module mods) /\
        exported_fallback mods exps = NONE` by
        (qpat_assum `calldata_dispatch_mods mods exps cd = NONE` mp_tac >>
         qpat_assum `(if LENGTH cd < 4 then NONE else _) = NONE`
           (fn hit => simp[NoAsms, calldata_dispatch_mods_def, LET_THM, hit]) >>
         Cases_on `exported_fallback mods exps` >> simp[]) >>
      `fb = NONE` by drule_all_then ACCEPT_TAC linked_classified_fallback_absent >>
      (Q.SUBGOAL_THEN `LENGTH cd < 4 \/ FIND
         (\(name,tys). abi_method_id (type_env_all_modules mods) name tys =
           cd_selector cd) (abi_deployed_signatures mods exps) = NONE` assume_tac
       >- (Cases_on `LENGTH cd < 4` >> fs[])) >>
      qpat_x_assum `fb = NONE` SUBST_ALL_TAC >>
      qunabbrev_tac `cd` >>
      mp_tac (Q.SPECL [`mods`,`exps`,`rpolicy`,`unit`,`am`,`tx`,`vs`,
          `exts`,`ints`,`ctor`,`imp_ctors`] lower_vyper_runtime_unit_linear_miss_reverts_mods) >>
      impl_tac >- asm_rewrite_tac[] >>
      disch_then (qx_choosel_then [`fn`,`s`,`G'`,`tn'`] strip_assume_tac) >>
      qexistsl_tac [`fn`,`s`,`G'`,`tn'`,`0`] >> asm_rewrite_tac[] >>
      qexists_tac `fuel` >> FIRST_ASSUM ACCEPT_TAC) >>
  PairCases_on `x` >>
  rename1 `(if LENGTH cd < 4 then NONE else _) = SOME (name,tys)` >>
  `4 <= LENGTH cd /\
    FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys =
      cd_selector cd) (abi_deployed_signatures mods exps) = SOME (name,tys)` by
    (Cases_on `LENGTH cd < 4` >> fs[arithmeticTheory.NOT_LESS]) >>
  qunabbrev_tac `cd` >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`,`ics` |-> `imp_ctors`]
    lower_vyper_runtime_unit_linear_hit_reverts_mods) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`fn`,`s`,`G'`,`tn'`] strip_assume_tac) >>
  qexistsl_tac [`fn`,`s`,`G'`,`tn'`,`0`] >> asm_rewrite_tac[] >>
  qexists_tac `fuel` >> FIRST_ASSUM ACCEPT_TAC
QED

Resume lower_vyper_runtime_unit_reverts_mods[grouped_rejection]:
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `?func s G' tn' marks.
     unit.cu_context.ctx_entry = SOME "__entry" /\
     venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
     fn_entry_label func = SOME "__entry" /\ s.vs_returndata = [] /\
     entry_prov func start FEMPTY = FEMPTY /\
     entry_taint_vars func start entry_taint = entry_taint /\
     (!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,func,[])
        (start,FEMPTY,entry_taint) marks (Abort Revert_abort s,G',tn'))`
    suffices_by
      (disch_then (qx_choosel_then [`func`,`s`,`G'`,`tn'`,`marks`] strip_assume_tac) >>
       qspecl_then [`unit.cu_context`,`func`,`vs`,`s`,`G'`,`tn'`,`marks`]
         mp_tac entry_joint_revert_exit >>
       qpat_assum `Abbrev (start = _)`
         (PURE_ONCE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
       (impl_tac >- asm_rewrite_tac[]) >>
       disch_then (map_every assume_tac o CONJUNCTS) >>
       qpat_assum `Abbrev (start = _)`
         (PURE_ONCE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
       qexistsl_tac [`func`,`s`,`G'`,`tn'`,`LENGTH marks`] >> asm_rewrite_tac[]) >>
  qabbrev_tac `groups = MAP (package_external_group_unit mods rpolicy.rpol_target T
    (K global_nonreentrant_slot)) exts` >>
  qabbrev_tac `ips = MAP (set_internal_package_target rpolicy.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0)
      (order_internals_unit
        (runtime_internal_order_unit (exported_runtime_fns mods exps)
          (main_module mods) ints) ints)` >>
  qabbrev_tac `fall = set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn_unit mods T (K global_nonreentrant_slot) fb)` >>
  `run_grouped_lowering groups ips fall rpolicy "__entry" = SOME unit` by
    gvs[lower_vyper_runtime_unit_mods_def, AllCaseEqs()] >>
  `EVERY group_entry_labels_ok groups` by
    simp[Abbr `groups`, EVERY_MAP, package_external_group_unit_labels] >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    (qunabbrev_tac `ips` >>
     qabbrev_tac `srcs = order_internals_unit
         (runtime_internal_order_unit (exported_runtime_fns mods exps) (main_module mods) ints) ints` >>
     qpat_x_assum `Abbrev (srcs = _)` kall_tac >>
     qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` kall_tac >>
     qid_spec_tac `srcs` >>
     Induct >- simp[internal_fn_descriptors_def] >>
     gen_tac >> PairCases_on `h` >>
     simp[package_internal_fn_unit_def, set_internal_package_target_def,
       internal_fn_descriptors_def] >>
     pure_rewrite_tac [internal_label_ok_def] >> irule internal_fn_label_prefix) >>
  drule_all grouped_internal_run_labels >>
  disch_then (qx_choosel_then [`compiled`,`final`,`data`] strip_assume_tac) >>
  `unit.cu_context.ctx_entry = SOME "__entry" /\
   ?fn. venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn` by
    (qpat_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
     simp[NoAsms, extract_context_with_internals_def] >> CASE_TAC >> simp[] >>
     rename1 `package_internal_blocks _ _ = SOME packed` >> PairCases_on `packed` >>
     simp[mk_venom_context_def, lookup_function_def, mk_raw_function_def, FIND_thm] >>
     disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> simp[FIND_thm]) >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all run_grouped_lowering_retained_entry_prefix >>
     disch_then (qx_choosel_then [`se`,`rest`] strip_assume_tac) >>
     `cs_extends (initial_compile_state "__entry") se` by
       (irule compile_grouped_runtime_extends >> qexistsl_tac [`fall`,`groups`,`[]`] >> simp[]) >>
     `MAP (\bb. bb.bb_label) (all_blocks (initial_compile_state "__entry")) =
      ["__entry"]` by simp[initial_compile_state_def, all_blocks_def] >>
     qpat_assum `cs_extends (initial_compile_state "__entry") se`
       (mp_tac o MATCH_MP block_labels_cs_extends) >>
     simp[] >> strip_tac >>
     Cases_on `all_blocks se` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  drule_all run_grouped_lowering_dispatch_code >>
  disch_then (qx_choosel_then [`sf`,`fl`,`jobs`,`sd`,`sx`,`sn`,`se`] strip_assume_tac) >>
  `!label bb. venomInst$lookup_block label fn.fn_blocks = SOME bb ==>
               phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule acceptedContextPhiTheory.lowering_context_ok_block_phi >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     first_assum ACCEPT_TAC) >>
  `start.vs_current_bb = "__entry" /\ start.vs_inst_idx = 0 /\
   start.vs_allocas = FEMPTY /\ start.vs_alloca_next = 0 /\
   allocas_below_fmp start /\ allocas_from 0 start /\
   ~start.vs_halted /\ fresh_vars_wrt sf start /\
   start.vs_call_ctx = vs.vs_call_ctx` by
    gvs[Abbr `start`, initial_venom_state_rel_mods_def, allocas_below_fmp_def,
        allocas_from_def, fresh_vars_wrt_def] >>
  `entry_prov fn start FEMPTY = FEMPTY /\
   entry_taint_vars fn start entry_taint = entry_taint` by
    (`?bb. venomInst$lookup_block "__entry" fn.fn_blocks = SOME bb` by
       (qpat_assum `fn_entry_label fn = SOME "__entry"` mp_tac >>
        Cases_on `fn.fn_blocks` >> simp[NoAsms, fn_entry_label_def, entry_block_def] >>
        simp[lookup_block_def, FIND_thm]) >>
     irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     qexists_tac `bb` >> simp[] >>
     qpat_assum `!label bb. venomInst$lookup_block label _ = SOME bb ==> _`
       (qspecl_then [`"__entry"`,`bb`] mp_tac) >> simp[]) >>
  `alloca_frontier_inv unit.cu_context fn ARB start /\
   unit_alloca_budget unit.cu_context < dimword (:256)` by
    (drule_all registration_empty_frontier >> disch_then irule >> simp[]) >>
  `alloca_inv start` by simp[alloca_inv_empty] >>
  `selected_registration_resources unit.cu_context fn ARB 0 sf start` by
    simp[selected_registration_resources_def] >>
  `fn_inst_ids_distinct fn` by
    (`MEM fn unit.cu_context.ctx_functions` by drule_then ACCEPT_TAC lookup_function_MEM >>
     drule lowering_context_ok_static_integrity >> strip_tac >>
     drule_all ctx_inst_ids_distinct_fn >>
     simp[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  `LENGTH start.vs_call_ctx.cc_calldata < dimword (:256)` by
    (simp[] >>
     gvs[source_typing_ok_mods_def, initial_venom_state_rel_mods_def, venom_env_rel_def] >>
     drule_all_then ACCEPT_TAC call_ctx_rel_calldata_length) >>
  `ctx_has_dalloca unit.cu_context ==>
     allocas_below_fmp start /\
     start.vs_alloca_next + pending_alloca_size fn start <= w2n start.vs_initial_fmp` by
    (strip_tac >>
     `start.vs_alloca_next + pending_alloca_size fn start <= unit_alloca_budget unit.cu_context` by
       (qpat_assum `alloca_frontier_inv _ _ _ _`
          (mp_tac o REWRITE_RULE [alloca_frontier_inv_def]) >>
        simp[deploy_ctor_pending_alloca_eq] >> decide_tac) >>
     fs[Abbr `start`] >> decide_tac) >>
  qabbrev_tac `cd = vs.vs_call_ctx.cc_calldata` >>
  `!name tys. MEM (name,tys) (abi_deployed_signatures mods exps) ==>
     ?tops top mut nr rr args dflts ret body prefix k.
       ALOOKUP mods (ALOOKUP exps name) = SOME tops /\ MEM top tops /\
       ((name <> "__default__" /\
         top = FunctionDecl External mut nr rr name args dflts ret body) \/
        public_getter_src (ALOOKUP exps name) top =
          SOME (mut,nr,rr,name,args,dflts,ret,body)) /\
       abi_decl_signatures top = abi_function_signatures name args dflts /\
       MEM (prefix,k) (abi_entries args dflts) /\ tys = MAP SND prefix /\
       MEM (ALOOKUP exps name,
         subst_consts_fn_mods (consts_env_mods mods) (mut,nr,rr,name,args,dflts,ret,body)) exts` by
    (rpt gen_tac >> strip_tac >>
     drule_all (SRULE [LET_THM] deployed_signature_selected_module) >>
     strip_tac >>
     rename1 `MEM (name,tys) (abi_decl_signatures top)` >>
     rename1 `ALOOKUP mods (ALOOKUP exps name) = SOME src_tops` >>
     (Q.SUBGOAL_THEN `?mut nr rr args dflts ret rawbody.
        (name <> "__default__" /\
         top = FunctionDecl External mut nr rr name args dflts ret rawbody) \/
        public_getter_src (ALOOKUP exps name) top =
          SOME (mut,nr,rr,name,args,dflts,ret,rawbody)`
        (qx_choosel_then [`mut`,`nr`,`rr`,`args`,`dflts`,`ret`,`rawbody`] assume_tac)
      >- (qpat_x_assum `MEM (name,tys) (abi_decl_signatures top)` mp_tac >>
        Cases_on `top` >> simp[abi_decl_signatures_def]
        >- (Cases_on `f` >> simp[abi_decl_signatures_def] >>
            IF_CASES_TAC >> simp[abi_function_signatures_def, MEM_MAP, EXISTS_PROD] >>
            strip_tac >> gvs[] >> metis_tac[])
        >- (Cases_on `v` >> simp[abi_decl_signatures_def, public_getter_src_def] >>
            rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[]) >>
        Cases_on `v` >> simp[abi_decl_signatures_def, public_getter_src_def] >>
        rpt strip_tac >> gvs[] >> pairarg_tac >> simp[])) >>
     `abi_decl_signatures top = abi_function_signatures name args dflts` by
       (qpat_assum `(name <> "__default__" /\ _) \/ _` strip_assume_tac
        >- gvs[abi_decl_signatures_def] >>
        drule tagged_getter_decl_signature >> simp[abi_function_signatures_def] >>
        fs[tagged_getter_source_tuple] >>
        drule external_getter_defaults >> simp[abi_entries_no_defaults]) >>
     drule_all_then assume_tac selected_external_member_with_defaults_mods >>
     qpat_x_assum `MEM (name,tys) (abi_decl_signatures top)` mp_tac >>
     qpat_assum `abi_decl_signatures top = _` (fn eq =>
       simp[NoAsms, eq, abi_function_signatures_def, MEM_MAP, EXISTS_PROD]) >>
     disch_then (qx_choosel_then [`pref`,`k`] strip_assume_tac) >>
     qexistsl_tac [`src_tops`,`top`,`mut`,`nr`,`rr`,`args`,`dflts`,`ret`,`rawbody`,`pref`,`k`] >>
     asm_rewrite_tac[abi_function_signatures_def]) >>
  `!tops mut nr rr name args ds ret body pref k.
     MEM (mut,nr,rr,name,args,ds,ret,body)
       (FST (FOLDR classify_function ([],[],NONE,NONE) tops)) /\
     MEM (pref,k) (abi_entries args ds) ==>
     MEM (name,MAP SND pref) (abi_external_signatures tops)` by
    (rpt (pop_assum kall_tac) >> Induct >> simp[abi_external_signatures_def] >>
     qx_gen_tac `top` >> simp[checkedSelectorTablePropsTheory.classify_function_external_component] >>
     Cases_on `top` >> simp[] >> BasicProvers.every_case_tac >> gvs[] >> rpt strip_tac >>
     gvs[abi_decl_signatures_def, abi_function_signatures_def, MEM_MAP, EXISTS_PROD] >>
     metis_tac[abi_external_signatures_def]) >>
  `!tag src tops key mut nr rr name args ds ret body pref k.
     MEM (tag,(mut,nr,rr,name,args,ds,ret,body)) (exported_fn src tops key) /\
     MEM (pref,k) (abi_entries args ds) ==>
     name = key /\ MEM (name,MAP SND pref) (abi_external_signatures tops)` by
    (qpat_x_assum `!tops mut nr rr name args ds ret body pref k. _` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >>
     rpt gen_tac >> simp[exported_fn_def] >> pairarg_tac >> gvs[] >>
     rename1 `FOLDR classify_function _ ts = (raw,_,_,_)` >>
     Cases_on `FILTER (\f. fn_decl_name f = key) raw` >> gvs[]
     >- (Cases_on `FILTER (\g. fn_decl_name g = key)
          (FLAT (MAP (\t. case public_getter_src src t of
                            NONE => [] | SOME g => [g]) ts))` >> gvs[] >>
         strip_tac >> gvs[] >>
         rename1 `FILTER _ _ = (mut,nr,rr,name,args,ds,ret,fbody)::_` >>
         qpat_assum `FILTER _ _ = _ :: _`
           (mp_tac o Q.AP_TERM `MEM (mut,nr,rr,name,args,ds,ret,fbody)`) >>
         simp[MEM_FILTER, fn_decl_name_def, MEM_FLAT, MEM_MAP, AllCaseEqs()] >>
         strip_tac >> gvs[] >>
         rename1 `public_getter_src src top = SOME _` >>
         drule tagged_getter_decl_signature >> strip_tac >>
         qpat_assum `public_getter_src src top = SOME _`
           (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]) >>
         drule_then assume_tac external_getter_defaults >>
         gvs[abi_entries_no_defaults] >>
         simp[abi_external_signatures_def, MEM_FLAT, MEM_MAP] >>
         qexists_tac `abi_decl_signatures top` >>
         conj_tac >- (qexists_tac `top` >> simp[]) >> simp[]) >>
     strip_tac >> gvs[] >>
     rename1 `FILTER _ _ = (mut,nr,rr,name,args,ds,ret,fbody)::_` >>
     qpat_assum `FILTER _ _ = _ :: _`
       (mp_tac o Q.AP_TERM `MEM (mut,nr,rr,name,args,ds,ret,fbody)`) >>
     simp[MEM_FILTER, fn_decl_name_def] >>
     strip_tac >> gvs[] >>
     qpat_assum `!tops mut nr rr name args ds ret body pref k. _`
       (qspecl_then [`ts`,`mut`,`nr`,`rr`,`key`,`args`,`ds`,`ret`,`fbody`,`pref`,`k`] mp_tac) >>
     simp[]) >>
  `!exports src mut nr rr name args ds ret body pref k.
     MEM (src,(mut,nr,rr,name,args,ds,ret,body)) (exported_fns mods exports) /\
     MEM (pref,k) (abi_entries args ds) ==>
     MEM (name,MAP SND pref)
       (FLAT (MAP (\(key,owner). case ALOOKUP mods (SOME owner) of
          NONE => [] | SOME declarations => FILTER (\(nm,tys). nm = key)
            (abi_external_signatures declarations)) exports))` by
    (qpat_x_assum `!tag src tops key mut nr rr name args ds ret body pref k. _` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >>
     Induct >> simp[exported_fns_def] >> qx_gen_tac `exp` >> PairCases_on `exp` >>
     simp[exported_fns_def] >> rpt gen_tac >>
     Cases_on `ALOOKUP mods (SOME exp1)` >> simp[MEM_FILTER] >>
     rpt strip_tac >>
     (qpat_assum `!src mut nr rr name args ds ret body pref k. _` drule_all >> simp[] >> NO_TAC
      ORELSE
      qpat_assum `!tag src tops key mut nr rr name args ds ret body pref k. _` drule_all >> simp[])) >>
  `!es. LENGTH (subst_consts_exprs_mods (consts_env_mods mods) es) = LENGTH es` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  `!src mut nr rr name args ds ret code pref k.
     MEM (src,(mut,nr,rr,name,args,ds,ret,code)) exts /\
     MEM (pref,k) (abi_entries args ds) ==>
     MEM (name,MAP SND pref) (abi_deployed_signatures mods exps)` by
    (rpt gen_tac >>
     qpat_assum `classify_functions_unit mods exps = _` mp_tac >>
     simp[NoAsms, classify_functions_unit_def] >> pairarg_tac >>
     first_assum (fn th => simp[NoAsms,th]) >>
     disch_then (SUBST1_TAC o SYM o CONJUNCT1) >>
     simp[NoAsms, MEM_MAP, MEM_APPEND, EXISTS_PROD, MAP_MAP_o, combinTheory.o_DEF] >>
     strip_tac >>
     rename1 `_ = subst_consts_fn_mods _ (_,_,_,_,_,raw_ds,_,_)` >>
     `MEM (pref,k) (abi_entries args raw_ds)` by
       gvs[subst_consts_fn_mods_def, abi_entries_member] >>
     gvs[subst_consts_fn_mods_def] >>
     simp[abi_deployed_signatures_def]
     >- (disj2_tac >>
         qpat_assum `!exports src mut nr rr name args ds ret body pref k. _` drule_all >> simp[]) >>
     disj1_tac >>
     `MEM (name,MAP SND pref) (abi_external_signatures (main_module mods))` suffices_by
       (Cases_on `ALOOKUP mods NONE` >> simp[main_module_def, abi_external_signatures_def])
     >- (qpat_assum `!tops mut nr rr name args ds ret body pref k. MEM _ (FST _) /\ _ ==> _`
           (qspec_then `main_module mods` mp_tac) >>
         simp[] >> disch_then drule_all >> simp[]) >>
     fs[MEM_public_getters] >>
     rename1 `public_getter top = SOME _` >>
     drule publicGetterPropsTheory.public_getter_defaults >> strip_tac >>
     drule publicGetterPropsTheory.public_getter_signature >> strip_tac >>
     gvs[abi_entries_no_defaults, abi_external_signatures_def, MEM_FLAT, MEM_MAP] >>
     qexists_tac `abi_decl_signatures top` >>
     conj_tac >- (qexists_tac `top` >> simp[]) >> simp[]) >>
  `!src mut nr rr name args ds ret code.
     MAP FST (external_group_selectors
       (package_external_group_unit mods rpolicy.rpol_target T
         (K global_nonreentrant_slot) (src,(mut,nr,rr,name,args,ds,ret,code)))) =
     MAP (\(nm,tys). abi_method_id (type_env_all_modules mods) nm tys)
       (abi_function_signatures name args ds)` by
    (rpt (pop_assum kall_tac) >> rpt gen_tac >> Cases_on `ds` >>
     simp[package_external_group_unit_def, package_external_fn_unit_def,
          set_external_package_target_def, external_group_selectors_def,
          compute_selector_method_id, abi_function_signatures_def, abi_entries_no_defaults,
          MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, FORALL_PROD]) >>
  `!ks id. MEM id (MAP FST (grouped_selectors
       (MAP (package_external_group_unit mods rpolicy.rpol_target T
          (K global_nonreentrant_slot)) ks))) ==>
     ?key nm ts pref k. MEM key ks /\ fn_decl_name (SND key) = nm /\ ts = MAP SND pref /\
        (?src m n r args ds rt code. key = (src,(m,n,r,nm,args,ds,rt,code)) /\
          MEM (pref,k) (abi_entries args ds)) /\
        id = abi_method_id (type_env_all_modules mods) nm ts` by
    (rpt gen_tac >> simp[grouped_selectors_def, MAP_FLAT, MEM_FLAT, MEM_MAP] >>
     strip_tac >> rename1 `MEM key ks` >> PairCases_on `key` >>
     `MEM id (MAP FST (external_group_selectors
        (package_external_group_unit mods rpolicy.rpol_target T
          (K global_nonreentrant_slot)
          (key0,key1,key2,key3,key4,key5,key6,key7,key8))))` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     qpat_x_assum `MEM id (MAP FST (external_group_selectors _))` mp_tac >>
     qpat_assum `!src mut nr rr name args ds ret code. MAP FST _ = _`
       (fn eq => pure_rewrite_tac[eq, abi_function_signatures_def, MAP_MAP_o,
                                  combinTheory.o_DEF] >> simp[NoAsms, MEM_MAP, EXISTS_PROD]) >>
     disch_then (qx_choosel_then [`sig_args`,`nk`] strip_assume_tac) >>
     qexistsl_tac [`key0`,`key1`,`key2`,`key3`,`key4`,`key5`,`key6`,`key7`,`key8`,
                   `sig_args`,`nk`] >>
     fs[fn_decl_name_def]) >>
  `!ks. EVERY (\(sel,_,_). sel < dimword (:256))
          (grouped_selectors (MAP (package_external_group_unit mods rpolicy.rpol_target T
            (K global_nonreentrant_slot)) ks))` by
    (gen_tac >> simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     rename1 `MEM (sel,lbl,tz) _` >>
     `MEM sel (MAP FST (grouped_selectors
       (MAP (package_external_group_unit mods rpolicy.rpol_target T
         (K global_nonreentrant_slot)) ks)))` by (simp[MEM_MAP] >> qexists_tac `(sel,lbl,tz)` >> simp[]) >>
     qpat_assum `!ks id. MEM id _ ==> _` drule >>
     disch_then (qx_choosel_then [`key`,`nm`,`ts`,`pf`,`nk`] strip_assume_tac) >>
     simp[abi_method_id_def, GSYM calldata_method_id_four_bytes, w2n_lt]) >>
  `!common entries specs off. MEM (ExternalDefaults common entries specs off) groups ==>
     EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs` by
    (rpt gen_tac >> simp[Abbr `groups`, MEM_MAP] >>
     disch_then (qx_choose_then `key0` strip_assume_tac) >> PairCases_on `key0` >>
     rename1 `MEM (src,m,n,r,nm,aa,ds,rt,code) exts` >>
     qpat_assum `ExternalDefaults _ _ _ _ = _` (assume_tac o SYM) >>
     drule_all classified_grouped_default_compile_inputs_mods >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all classified_external_default_source_mods >>
     disch_then (qx_choosel_then [`declarations`,`raw_ds`,`raw_code`] strip_assume_tac) >>
     `?art. check_contract F am.layouts tx.target mods = SOME art /\
       exports_ok am.layouts tx.target mods exps` by fs[source_typing_ok_mods_def] >>
     `module_allocated am.layouts tx.target src declarations` by
       drule_all_then ACCEPT_TAC classified_external_owner_allocated_mods >>
     `LENGTH ds <= LENGTH aa` by
       (`ds = subst_consts_exprs_mods (consts_env_mods mods) raw_ds` by
           fs[subst_consts_fn_mods_def] >>
        drule_all grouped_checked_default_syntax_mods >> simp[]) >>
     qabbrev_tac `alloc_env = build_compile_env_unit mods src Internal m nm aa rt code F` >>
     `common.ec_env.ce_struct_fields = alloc_env.ce_struct_fields` by
       (qunabbrev_tac `alloc_env` >>
        qpat_assum `ExternalDefaults _ _ _ _ = package_external_group_unit _ _ _ _ _` mp_tac >>
        qpat_assum `ds <> []` mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
        Cases_on `rt = NoneT` >>
        simp[package_external_group_unit_def, package_external_fn_unit_def,
             set_external_package_target_def, update_cenv_ret_abi_def,
             update_cenv_nonreentrant_def, NULL_EQ] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `common = _` SUBST1_TAC >>
        simp[build_compile_env_unit_def, ELIM_UNCURRY]) >>
     `type_memory_bytes common.ec_env = type_memory_bytes alloc_env` by
       (irule type_memory_bytes_frame >> simp[]) >>
     `EVERY (\(_,ty). type_memory_bytes alloc_env ty < 2 ** 64) aa` by
       (qpat_assum `fn_allocs_ok_unit _ _` mp_tac >>
        simp[NoAsms, fn_allocs_ok_unit_def] >> simp[Abbr `alloc_env`]) >>
     simp[NoAsms, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     rename1 `MEM (param,ty,x) specs` >>
     `(param,ty) ∈ set aa` by
       (irule rich_listTheory.MEM_DROP_IMP >>
        qexists_tac `LENGTH aa - LENGTH ds` >>
        qpat_x_assum `MEM (param,ty,x) specs` mp_tac >>
        qpat_assum `specs = MAP _ _` SUBST1_TAC >>
        pure_rewrite_tac [MEM_MAP] >> simp[NoAsms, EXISTS_PROD] >>
        rpt strip_tac >> gvs[] >>
        `LENGTH (DROP (LENGTH aa - LENGTH ds) aa) = LENGTH ds` by simp[LENGTH_DROP] >>
        qpat_x_assum `MEM _ (ZIP _)` mp_tac >>
        simp[MEM_ZIP] >> disch_then (qx_choose_then `idx` strip_assume_tac) >>
        simp[MEM_EL] >> qexists_tac `idx` >> simp[]) >>
     qpat_assum `EVERY (\(_,ty). _) aa` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(param,ty)` mp_tac) >> simp[dimword_def]) >>
  reverse (Cases_on `if LENGTH cd < 4 then NONE
    else FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys =
      cd_selector cd) (abi_deployed_signatures mods exps)`)
  >- (
      PairCases_on `x` >>
      rename1 `(if LENGTH cd < 4 then NONE else _) = SOME (name,tys)` >>
      `4 <= LENGTH cd /\
        FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys =
          cd_selector cd) (abi_deployed_signatures mods exps) = SOME (name,tys)` by
        (Cases_on `LENGTH cd < 4` >> fs[arithmeticTheory.NOT_LESS]) >>
      `MEM (name,tys) (abi_deployed_signatures mods exps)` by
        (drule FIND_MEM >> simp[]) >>
      qpat_assum `!name tys. MEM (name,tys) (abi_deployed_signatures mods exps) ==> _`
        (qspecl_then [`name`,`tys`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qx_choosel_then [`src_tops`,`top`,`mut`,`nr`,`rr`,`args`,`dflts`,
        `ret`,`rawbody`,`pref`,`k`] (map_every assume_tac o CONJUNCTS)) >>
      `k <= LENGTH dflts /\ pref = TAKE (LENGTH args - LENGTH dflts + k) args` by
        fs[abi_entries_member] >>
      `abi_method_id (type_env_all_modules mods) name tys = cd_selector cd` by
        (drule venomInstTheory.FIND_P >> simp[]) >>
      `params_ok (type_env_all_modules mods) args` by
        (irule linkedExternalParameterTypesTheory.checked_external_parameter_types_mods >>
         rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
      (Q.SUBGOAL_THEN `OPT_MMAP (evaluate_type (type_env_all_modules mods)) tys = NONE \/
         ?tvs. OPT_MMAP (evaluate_type (type_env_all_modules mods)) tys = SOME tvs /\
           (LENGTH cd < 4 + SUM (MAP tv_abi_size tvs) \/
            calldata_decode_args cd tvs 0 = NONE)` assume_tac
       >- (qpat_assum `calldata_dispatch_mods mods exps cd = NONE` mp_tac >>
           qpat_assum `(if LENGTH cd < 4 then NONE else _) = SOME (name,tys)`
             (fn hit => simp[NoAsms, calldata_dispatch_mods_def, LET_THM, hit]) >>
           Cases_on `OPT_MMAP (evaluate_type (type_env_all_modules mods)) tys` >> simp[] >>
           rename1 `OPT_MMAP _ _ = SOME tvs` >>
           Cases_on `LENGTH cd < 4 + SUM (MAP tv_abi_size tvs)` >> simp[] >>
           Cases_on `calldata_decode_args cd tvs 0` >> simp[])) >>
      qabbrev_tac `tenv = type_env_all_modules mods` >>
      `?all_tvs. LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv)
          (MAP SND args) all_tvs` by
        (irule vyperTypeArgFitsTheory.well_formed_types_evaluate >>
         fs[vyperTypeContractTheory.params_ok_def, EVERY_MAP, EVERY_MEM,
            FORALL_PROD, combinTheory.o_DEF] >>
         metis_tac[vyperTypeSystemTheory.assignable_type_well_formed]) >>
      `OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME all_tvs` by
        (simp[vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_EL,
           LIST_EQ_REWRITE] >> fs[LIST_REL_EL_EQN, EL_MAP] >>
         rpt strip_tac >> first_x_assum (drule_then assume_tac) >> gvs[]) >>
      qabbrev_tac `npos = LENGTH args - LENGTH dflts` >>
      qabbrev_tac `tvs = TAKE (npos + k) all_tvs` >>
      `OPT_MMAP (evaluate_type tenv) tys = SOME tvs` by
        (simp[Abbr `tvs`, Abbr `npos`, MAP_TAKE] >>
         irule groupedDefaultArgumentsTheory.opt_mmap_take_some >>
         first_assum ACCEPT_TAC) >>
      (Q.SUBGOAL_THEN `LENGTH cd < 4 + SUM (MAP tv_abi_size tvs) \/
          calldata_decode_args cd tvs 0 = NONE` assume_tac
       >- (qpat_x_assum `OPT_MMAP _ _ = NONE \/ _` mp_tac >> simp[])) >>
      qabbrev_tac `src = ALOOKUP exps name` >>
      qabbrev_tac `key = (src,subst_consts_fn_mods (consts_env_mods mods)
           (mut,nr,rr,name,args,dflts,ret,rawbody))` >>
      `MEM key exts` by simp[Abbr `key`, Abbr `src`] >>
      qabbrev_tac `grp = package_external_group_unit mods rpolicy.rpol_target T
        (K global_nonreentrant_slot) key` >>
      `MEM grp groups` by (simp[Abbr `groups`, Abbr `grp`, MEM_MAP] >> metis_tac[]) >>
      `ALL_DISTINCT (MAP (fn_decl_name o SND) exts)` by
        (drule_all defaultDispatchModsNamesTheory.linked_package_labels_distinct >>
         disch_then (qspec_then `rpolicy.rpol_target` mp_tac) >>
         `!entry. FST (set_external_package_target rpolicy.rpol_target
             (package_external_fn_unit mods T (K global_nonreentrant_slot) entry)) =
           "fn_" ++ fn_decl_name (SND entry)` by
           (Cases >> rename1 `FST (_ (_ (_,funrec))) = _` >> PairCases_on `funrec` >>
            simp[package_external_fn_unit_def, set_external_package_target_def, fn_decl_name_def]) >>
         simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >>
         irule (Q.ISPEC `STRCAT "fn_"` ALL_DISTINCT_MAP) >>
         simp[MAP_MAP_o, combinTheory.o_DEF]) >>
      `!nm ts. MEM (nm,ts) (abi_deployed_signatures mods exps) /\
         abi_method_id tenv nm ts = cd_selector cd ==> nm = name /\ ts = tys` by
        (rpt gen_tac >> strip_tac >>
         `ALL_DISTINCT (MAP (\(nm,ts). abi_method_id tenv nm ts)
            (abi_deployed_signatures mods exps))` by
           fs[source_typing_ok_mods_def, vyperTypeContractTheory.exports_ok_def,
           Abbr `tenv`] >>
         `(nm,ts) = (name,tys)` by
           (drule mem2varProofsTheory.ALL_DISTINCT_MAP_IMP >>
            disch_then (qspecl_then [`(nm,ts)`,`(name,tys)`] mp_tac) >> simp[]) >>
         qpat_x_assum `(nm,ts) = (name,tys)` mp_tac >> simp[]) >>
      `?pkeys skeys. exts = pkeys ++ key::skeys` by
        (pure_rewrite_tac[GSYM MEM_SPLIT] >> first_assum ACCEPT_TAC) >>
      qabbrev_tac `pre = MAP (package_external_group_unit mods rpolicy.rpol_target T
        (K global_nonreentrant_slot)) pkeys` >>
      qabbrev_tac `post = MAP (package_external_group_unit mods rpolicy.rpol_target T
        (K global_nonreentrant_slot)) skeys` >>
      `groups = pre ++ grp::post` by simp[Abbr `groups`, Abbr `pre`, Abbr `post`, Abbr `grp`] >>
      `fn_decl_name (SND key) = name` by simp[Abbr `key`, subst_consts_fn_mods_def, fn_decl_name_def] >>
      `!x. MEM x pkeys ==> MEM x exts` by simp[] >>
      `~MEM (cd_selector cd) (MAP FST (grouped_selectors pre))` by
        (simp[Abbr `pre`] >> strip_tac >>
         qpat_assum `!ks id. MEM id _ ==> _` drule >>
         disch_then (qx_choosel_then [`other`,`nm`,`ts`,`pf`,`nk`] strip_assume_tac) >>
         `MEM other exts` by simp[] >>
         `MEM (nm,ts) (abi_deployed_signatures mods exps)` by
           (qpat_assum `other = _` SUBST_ALL_TAC >>
            qpat_assum `!src mut nr rr name args ds ret code pref k. MEM _ exts /\ _ ==> _`
              drule_all >> simp[]) >>
         `nm = name` by
           (qpat_assum `!nm ts. MEM _ (abi_deployed_signatures _ _) /\ _ ==> _`
             (qspecl_then [`nm`,`ts`] mp_tac) >> simp[]) >>
         `MEM name (MAP (fn_decl_name o SND) pkeys)` by
           (simp[MEM_MAP] >> qexists_tac `other` >> simp[]) >>
         qpat_x_assum `ALL_DISTINCT (MAP (fn_decl_name o SND) exts)` mp_tac >>
         simp[ALL_DISTINCT_APPEND] >> disj2_tac >> disj2_tac >>
         qexists_tac `name` >> simp[]) >>
      `4 <= LENGTH start.vs_call_ctx.cc_calldata /\
       cd_selector cd = w2n (calldata_method_id start.vs_call_ctx.cc_calldata)` by
        simp[Abbr `cd`, calldataSelectorPropsTheory.cd_selector_method_id] >>
      `EVERY (\group. case group of ExternalSingle (sel,lbl,tz) pkg =>
        calldata_method_id start.vs_call_ctx.cc_calldata <> n2w sel
      | ExternalDefaults common entries _ _ =>
        FIND (\(sel,_,_,_). calldata_method_id start.vs_call_ctx.cc_calldata = n2w sel)
           entries = NONE) pre` by
        (irule groupedEntryPackageTheory.grouped_selector_misses >>
         qpat_assum `cd_selector cd = _` (fn eq => pure_rewrite_tac[GSYM eq]) >>
         simp[Abbr `pre`] >> qpat_assum `~MEM (cd_selector cd) _` mp_tac >>
         simp[NoAsms, Abbr `pre`]) >>
      `EVERY (\group. case group of ExternalSingle (sel,lbl,tz) pkg =>
        calldata_method_id start.vs_call_ctx.cc_calldata <> n2w sel
      | ExternalDefaults common entries specs _ =>
        FIND (\(sel,_,_,_). calldata_method_id start.vs_call_ctx.cc_calldata = n2w sel)
           entries = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs) pre` by
        (simp[EVERY_MEM] >> qx_gen_tac `g` >> strip_tac >>
         qpat_assum `EVERY _ pre` (mp_tac o Q.SPEC `g` o REWRITE_RULE [EVERY_MEM]) >>
         Cases_on `g` >> simp[] >>
         rename1 `MEM (ExternalDefaults c es sp hd) pre` >>
         `MEM (ExternalDefaults c es sp hd) groups` by simp[] >>
         qpat_assum `!common entries specs off. MEM (ExternalDefaults _ _ _ _) groups ==> _`
           (qspecl_then [`c`,`es`,`sp`,`hd`] mp_tac) >> simp[EVERY_MEM]) >>
      reverse (Cases_on `dflts = []`)
      >- (
      qabbrev_tac `pos_tvs = TAKE npos tvs` >>
      qabbrev_tac `kw_tvs = DROP npos tvs` >>
      `?art. check_contract F am.layouts tx.target mods = SOME art /\
             exports_ok am.layouts tx.target mods exps` by
        (qpat_assum `source_typing_ok_mods _ _ _ _` mp_tac >>
         simp[NoAsms, source_typing_ok_mods_def] >>
         disch_then (qx_choose_then `a` strip_assume_tac) >> qexists_tac `a` >> simp[]) >>
      `MEM (FunctionDecl External mut nr rr name args dflts ret rawbody) src_tops` by
        (qpat_assum `(name <> "__default__" /\ _) \/ _` strip_assume_tac
         >- (qpat_assum `top = FunctionDecl _ _ _ _ _ _ _ _ _`
               (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
         qpat_assum `public_getter_src _ _ = SOME _`
           (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]) >>
         drule external_getter_defaults >> simp[]) >>
      qabbrev_tac `ds = subst_consts_exprs_mods (consts_env_mods mods) dflts` >>
      qabbrev_tac `code = subst_consts_stmts_mods (consts_env_mods mods) rawbody` >>
      `key = (src,(mut,nr,rr,name,args,ds,ret,code))` by
        simp[Abbr `key`, Abbr `ds`, Abbr `code`, subst_consts_fn_mods_def] >>
      `MEM (src,(mut,nr,rr,name,args,ds,ret,code)) exts` by
        (qpat_assum `key = (src,_)` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      `module_allocated am.layouts tx.target src src_tops` by
        drule_all_then ACCEPT_TAC classified_external_owner_allocated_mods >>
      `ds <> [] /\ LENGTH ds = LENGTH dflts` by
        (`!es. LENGTH (subst_consts_exprs_mods (consts_env_mods mods) es) = LENGTH es` by
            (Induct >> simp[subst_consts_expr_mods_def]) >>
         `LENGTH ds = LENGTH dflts` by simp[Abbr `ds`] >>
         conj_tac >- (qpat_assum `dflts <> []` mp_tac >>
           qpat_assum `LENGTH ds = LENGTH dflts` (fn eq =>
             pure_rewrite_tac[GSYM LENGTH_NIL, GSYM eq]) >> simp[NoAsms]) >>
         first_assum ACCEPT_TAC) >>
      `LENGTH ds <= LENGTH args /\
       MAP expr_type ds = MAP SND (DROP npos args) /\
       EVERY (runtime_constant_expr mods) ds /\ well_typed_exprs (artifact_env art mods src) ds` by
        (qunabbrev_tac `npos` >>
         qpat_assum `Abbrev (ds = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         drule_all grouped_checked_default_syntax_mods >>
         qpat_assum `LENGTH ds = LENGTH dflts` (fn eq => simp[NoAsms, eq])) >>
      qabbrev_tac `shadow_groups = MAP (\group. case group of
        ExternalSingle selector package =>
          ExternalSingle selector (gas_shadow_external_package package)
      | ExternalDefaults c es sp head =>
          ExternalDefaults (c with <|ec_env := gas_shadow_env T c.ec_env;
                                     ec_body := MAP gas_shadow_stmt c.ec_body|>)
            es (MAP (\(nm,ty,e). (nm,ty,gas_shadow_expr e)) sp) head) groups` >>
      `?shadow_unit.
        run_grouped_lowering shadow_groups (MAP gas_shadow_internal_package ips)
          (OPTION_MAP gas_shadow_fallback_package fall) rpolicy "__entry" = SOME shadow_unit /\
        gas_shadow_unit unit shadow_unit /\
        shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context` by
        (rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
         drule_all_then ACCEPT_TAC grouped_runtime_shadow_body_inv_mods) >>
      `?common entries specs off.
         grp = ExternalDefaults common entries specs off` by
        (qpat_assum `key = (src,_)` (fn eq => simp[Abbr `grp`, eq,
           package_external_group_unit_def, NULL_EQ]) >> pairarg_tac >> simp[]) >>
      `package_external_group_unit mods rpolicy.rpol_target T
          (K global_nonreentrant_slot) (src,(mut,nr,rr,name,args,ds,ret,code)) =
        ExternalDefaults common entries specs off` by
        (qpat_assum `key = (src,_)` (SUBST1_TAC o SYM) >> simp[markerTheory.Abbrev_def]) >>
      drule_all classified_grouped_default_compile_inputs_mods >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `MEM (pref,k) (abi_entries args ds)` by
        (simp[abi_entries_member, Abbr `npos`]) >>
      `abi_method_id (type_env_all_modules mods) name (MAP SND pref) = cd_selector cd` by
        (qpat_assum `abi_method_id tenv name tys = _` mp_tac >>
         qpat_assum `tys = MAP SND pref` (fn eq => pure_rewrite_tac[eq]) >>
         qunabbrev_tac `tenv` >> simp[NoAsms]) >>
      `entries = MAP (\(p,j). (abi_method_id tenv name (MAP SND p),
           external_prefix_label name j,min_calldata_size common.ec_env p 0,j))
         (abi_entries args ds)` by
        (qunabbrev_tac `tenv` >>
         qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _`
           (mp_tac o REWRITE_RULE [package_external_group_unit_def]) >>
         Cases_on `ret = NoneT` >>
         pop_assum (fn return => qpat_assum `ds <> []` (fn nonempty =>
           simp[NoAsms, return, nonempty, package_external_fn_unit_def,
                set_external_package_target_def, LET_THM, compute_selector_method_id,
                update_cenv_ret_abi_def, update_cenv_nonreentrant_def, NULL_EQ])) >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `_ = common` (fn eq => pure_rewrite_tac[GSYM eq]) >>
         qpat_assum `MAP _ _ = entries` (fn eq => pure_rewrite_tac[GSYM eq]) >>
         simp[NoAsms]) >>
      `MEM (cd_selector cd,external_prefix_label name k,
            min_calldata_size common.ec_env pref 0,k) entries` by
        (qpat_assum `entries = MAP _ _` SUBST1_TAC >>
         pure_rewrite_tac[MEM_MAP] >> qexists_tac `(pref,k)` >>
         simp[Abbr `tenv`]) >>
      `!p j. MEM (p,j) (abi_entries args ds) /\
           calldata_method_id start.vs_call_ctx.cc_calldata =
             n2w (abi_method_id tenv name (MAP SND p)) ==> p = pref /\ j = k` by
        (rpt gen_tac >> strip_tac >>
         `abi_method_id tenv name (MAP SND p) < dimword (:256)` by
           simp[NoAsms, abi_method_id_def, GSYM calldata_method_id_four_bytes, w2n_lt] >>
         `abi_method_id tenv name (MAP SND p) = cd_selector cd` by
           (qpat_assum `calldata_method_id _ = n2w _`
              (fn eq => pure_rewrite_tac[GSYM eq]) >>
            qpat_assum `cd_selector cd = w2n _`
              (fn eq => pure_rewrite_tac[eq]) >>
            qpat_assum `calldata_method_id _ = n2w _`
              (fn eq => simp[eq, w2n_n2w])) >>
         `MEM (name,MAP SND p) (abi_deployed_signatures mods exps)` by
           (qpat_assum `!src mut nr rr name args ds ret code pref k. MEM _ exts /\ _ ==> _`
              drule_all >> simp[]) >>
         `MAP SND p = MAP SND pref` by
           (qpat_assum `!nm ts. MEM _ (abi_deployed_signatures _ _) /\ _ ==> _`
              (qspecl_then [`name`,`MAP SND p`] mp_tac) >>
            (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
            qpat_assum `tys = MAP SND pref` (fn eq => simp[NoAsms, eq])) >>
         `LENGTH p = LENGTH pref` by
           (pop_assum (mp_tac o AP_TERM ``LENGTH : type list -> num``) >> simp[NoAsms]) >>
         qpat_assum `MEM (p,j) (abi_entries args ds)`
           (strip_assume_tac o REWRITE_RULE [abi_entries_member]) >>
         `j = k` by
           (qpat_x_assum `LENGTH p = LENGTH pref` mp_tac >>
            qpat_assum `p = TAKE _ args` (fn eq => pure_rewrite_tac[eq]) >>
            qpat_assum `pref = TAKE _ args` (fn eq => pure_rewrite_tac[eq]) >>
            qpat_assum `LENGTH ds = LENGTH dflts` (fn eq => simp[NoAsms, eq, LENGTH_TAKE_EQ, Abbr `npos`]) >>
            simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
         simp[Abbr `npos`, arithmeticTheory.ADD_COMM]) >>
      `groups = pre ++ ExternalDefaults common entries specs off::post` by
        (qpat_assum `grp = ExternalDefaults _ _ _ _` (SUBST1_TAC o SYM) >>
         first_assum ACCEPT_TAC) >>
      `FIND (\(sel,_,_,_). calldata_method_id start.vs_call_ctx.cc_calldata = n2w sel)
          entries = SOME (cd_selector cd,external_prefix_label name k,
             min_calldata_size common.ec_env pref 0,k)` by
        (qabbrev_tac `P = \((sel,_,_,_):num # string # num # num).
              calldata_method_id start.vs_call_ctx.cc_calldata = n2w sel` >>
         qabbrev_tac `hit = (cd_selector cd,external_prefix_label name k,
                              min_calldata_size common.ec_env pref 0,k)` >>
         `P hit` by
           (qpat_assum `cd_selector cd = w2n _`
             (fn eq => simp[NoAsms, Abbr `P`, Abbr `hit`, eq])) >>
         `!e. MEM e entries /\ P e ==> e = hit` by
           (qpat_assum `entries = MAP _ _` SUBST1_TAC >>
            simp[NoAsms, MEM_MAP, PULL_EXISTS] >>
            rpt strip_tac >> rename1 `MEM y (abi_entries args ds)` >>
            PairCases_on `y` >>
            qpat_x_assum `P _` mp_tac >> simp[NoAsms, Abbr `P`] >> strip_tac >>
            qpat_assum `!p j. MEM (p,j) (abi_entries args ds) /\ _ ==> _`
              drule_all >> strip_tac >>
            rename1 `MEM (pp,jj) (abi_entries args ds)` >>
            qpat_assum `pp = pref` SUBST1_TAC >> qpat_assum `jj = k` SUBST1_TAC >>
            qpat_assum `abi_method_id (type_env_all_modules mods) name (MAP SND pref) = _`
              (fn eq => simp[NoAsms, Abbr `hit`, Abbr `tenv`, eq])) >>
         Cases_on `FIND P entries` >> simp[NoAsms]
         >- (qpat_x_assum `FIND P entries = NONE`
               (mp_tac o REWRITE_RULE [mem2varBlockSimHelpersTheory.FIND_NONE_EVERY,
                 EVERY_MEM, combinTheory.o_DEF]) >>
             disch_then (qspec_then `hit` mp_tac) >> simp[]) >>
         drule venomInstTheory.FIND_MEM >> drule venomInstTheory.FIND_P >> strip_tac >> strip_tac >>
         first_x_assum drule_all >> simp[NoAsms]) >>
      `common.ec_env.ce_struct_fields = make_struct_fields_map_mods mods /\
       common.ec_env.ce_flag_n_members = SND (build_flag_info_mods mods (K (K 0)) (K 0)) /\
       common.ec_payable = (mut = Payable) /\ off = min_calldata_size common.ec_env (TAKE npos args) 0` by
        (qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _`
           (mp_tac o REWRITE_RULE [package_external_group_unit_def]) >>
         Cases_on `ret = NoneT` >>
         pop_assum (fn rval => qpat_assum `ds <> []` (fn dsval =>
           simp[NoAsms, rval, dsval, package_external_fn_unit_def,
                set_external_package_target_def, LET_THM, update_cenv_ret_abi_def,
                update_cenv_nonreentrant_def, NULL_EQ, compute_selector_method_id])) >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `_ = common` (fn eq => pure_rewrite_tac[GSYM eq]) >>
         qpat_assum `_ = off` (fn eq => pure_rewrite_tac[GSYM eq]) >>
         qpat_assum `LENGTH ds = LENGTH dflts` (fn eq =>
           simp[NoAsms, eq, Abbr `npos`, build_compile_env_unit_def, ELIM_UNCURRY])) >>
      `exprSimAbiDecodeEntryMetadata$abi_decode_root_metadata common.ec_env tenv` by
        (qunabbrev_tac `tenv` >> irule linkedAbiDecodeMetadataTheory.linked_abi_decode_root_metadata >>
         rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
         qexists_tac `F` >> drule vyperTypeContractContextTheory.check_contract_namespaces_ok >>
         disch_then ACCEPT_TAC) >>
      `LIST_REL (\arg tv. abi_decoder_coherent common.ec_env tenv
           common.ec_env.ce_struct_fields (SND arg) tv) args all_tvs` by
        (qpat_assum `params_ok tenv args` (strip_assume_tac o REWRITE_RULE [vyperTypeContractTheory.params_ok_def]) >>
         qpat_assum `LIST_REL _ (MAP SND args) all_tvs`
           (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN, LENGTH_MAP]) >>
         simp[NoAsms, LIST_REL_EL_EQN] >> (conj_tac >- first_assum ACCEPT_TAC) >>
         rpt strip_tac >>
         `evaluate_type tenv (SND (EL n args)) = SOME (EL n all_tvs)` by
           (qpat_assum `!n. n < LENGTH args ==> (\ty tv. evaluate_type _ ty = _) _ _`
              (qspec_then `n` mp_tac) >>
            qpat_assum `n < LENGTH args` (fn th => simp[NoAsms, EL_MAP, th])) >>
         `assignable_type tenv (SND (EL n args))` by
           (qpat_assum `EVERY (\(_,ty). assignable_type tenv ty) args`
              (mp_tac o REWRITE_RULE [EVERY_EL]) >>
            disch_then (qspec_then `n` mp_tac) >> Cases_on `EL n args` >>
            qpat_assum `n < LENGTH args` (fn th => simp[NoAsms, th])) >>
         irule exprSimAbiDecodeEntryCoherenceTheory.abi_decode_root_coherent >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `?shadow_fn shjobs shd.
         lookup_function "__entry" shadow_unit.cu_context.ctx_functions = SOME shadow_fn /\
         gas_shadow_function fn shadow_fn /\
         compile_group_dispatch_linear shadow_groups fl sf = (shjobs,shd) /\
         fn_has_code sf shd shadow_fn` by
        (drule_all groupedRuntimeBodyCodeTheory.grouped_shadow_entry_dispatch >>
         qpat_assum `Abbrev (shadow_groups = _)`
           (fn eq => pure_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]) >>
         qpat_assum `run_grouped_lowering shadow_groups _ _ _ _ = SOME shadow_unit`
           (fn eq => simp[NoAsms, eq]) >>
         qpat_assum `fresh_label "fallback" _ = (fl,sf)` (fn eq => simp[NoAsms, eq]) >>
         disch_then strip_assume_tac >>
         rename1 `gas_shadow_function fn shfn` >>
         qexists_tac `shfn` >>
         qpat_assum `_.cs_current_bb = fl` (fn eq => pure_rewrite_tac[GSYM eq]) >>
         qpat_assum `compile_group_dispatch_linear shadow_groups _ sf = (_,_)`
           (fn eq => simp[NoAsms, eq]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `min_calldata_size common.ec_env pref 0 = 4 + SUM (MAP tv_abi_size tvs)` by
        (qpat_assum `pref = TAKE _ args` SUBST1_TAC >>
         qpat_assum `Abbrev (tvs = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         irule groupedDefaultArgumentsTheory.grouped_argument_min_calldata_size >>
         qexists_tac `tenv` >> first_assum ACCEPT_TAC) >>
      `EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs` by
        (qpat_assum `!common entries specs off. MEM (ExternalDefaults _ _ _ _) groups ==> _`
           (qspecl_then [`common`,`entries`,`specs`,`off`] mp_tac) >>
         impl_tac >- (qpat_assum `groups = pre ++ ExternalDefaults _ _ _ _::post`
           (fn eq => simp[NoAsms, eq])) >> simp[NoAsms]) >>
      `EVERY group_entry_labels_ok shadow_groups` by
        (simp[NoAsms, Abbr `shadow_groups`, EVERY_MAP, combinTheory.o_DEF, EVERY_MEM] >>
         qx_gen_tac `group` >> strip_tac >>
         qpat_assum `EVERY group_entry_labels_ok groups` (drule_then mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         Cases_on `group`
         >- (rename1 `group_entry_labels_ok (ExternalSingle _ pkg) ==> _` >>
             PairCases_on `pkg` >>
             simp[NoAsms, group_entry_labels_ok_def, gas_shadow_external_package_def]) >>
         simp[NoAsms, group_entry_labels_ok_def]) >>
      `min_calldata_size common.ec_env pref 0 < dimword (:256)` by
        (`?lbl pos m pay key' tr view rt.
           set_external_package_target rpolicy.rpol_target
             (package_external_fn_unit mods T (K global_nonreentrant_slot)
               (src,(mut,nr,rr,name,args,([]:expr list),ret,code))) =
               (lbl,common.ec_env,pos,m,pay,nr,key',tr,view,code,rt)` by
          (qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _`
             (mp_tac o REWRITE_RULE [package_external_group_unit_def]) >>
           Cases_on `ret = NoneT` >>
           pop_assum (fn rt => qpat_assum `ds <> []` (fn ne =>
             simp[NoAsms, rt, ne, package_external_fn_unit_def, set_external_package_target_def,
                  LET_THM, NULL_EQ, compute_selector_method_id])) >>
           disch_then (map_every assume_tac o CONJUNCTS) >>
           qpat_assum `_ = common` (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
         `params_ok (type_env_all_modules mods) args` by
           (qpat_assum `params_ok tenv args` mp_tac >> simp[NoAsms, Abbr `tenv`]) >>
         drule_then assume_tac vyperTypeContractContextTheory.check_contract_namespaces_ok >>
         drule_all linked_registration_package_inputs >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `?tvs. OPT_MMAP _ _ = SOME tvs /\ _`
           (qx_choose_then `full_tvs` strip_assume_tac) >>
         `full_tvs = all_tvs` by
           (qpat_assum `OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME all_tvs` mp_tac >>
            qpat_assum `OPT_MMAP (evaluate_type (type_env_all_modules mods)) _ = SOME full_tvs`
              (fn eq => simp[NoAsms, Abbr `tenv`, eq])) >>
         pop_assum SUBST_ALL_TAC >>
         `SUM (MAP tv_abi_size tvs) <= SUM (MAP tv_abi_size all_tvs)` by
           (simp[NoAsms, Abbr `tvs`, callRejectMemoryTheory.prefix_head_size_le]) >>
         qpat_assum `min_calldata_size common.ec_env pref 0 = _` SUBST1_TAC >>
         qpat_assum `m = 4 + SUM (MAP tv_abi_size all_tvs)` (SUBST1_TAC o SYM) >>
         qpat_assum `m < dimword (:256)` mp_tac >>
         qpat_assum `SUM (MAP tv_abi_size tvs) <= _` mp_tac >> decide_tac) >>
      `((~common.ec_payable /\ start.vs_call_ctx.cc_callvalue <> 0w) \/
        (4 < min_calldata_size common.ec_env pref 0 /\
         LENGTH start.vs_call_ctx.cc_calldata < min_calldata_size common.ec_env pref 0)) ==>
       ?z J tz. z.vs_returndata = [] /\
         !D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
           (start,FEMPTY,entry_taint) [] (Abort Revert_abort z,J,tz)` by
        (disch_tac >> drule_all grouped_dispatch_long_prelude >>
         disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
           (qx_choosel_then [`mid`,`prep`,`cut`,`br`,`before`,`Gb`,`tb`]
             (map_every assume_tac o CONJUNCTS))) >>
         qpat_x_assum `groups = pre ++ ExternalDefaults _ _ _ _::post` SUBST_ALL_TAC >>
         drule_all compile_external_groups_selected_default_origin >>
         disch_then (qspecl_then [`[]`,`Gb`]
           (qx_choosel_then [`vars`,`checks`,`init`,`done`,`hit`,`Gh`,`th`]
            (map_every assume_tac o CONJUNCTS))) >>
         `hit.vs_call_ctx = start.vs_call_ctx` by
           (qpat_assum `selected_registration_frame before tb hit th` mp_tac >>
            qpat_assum `selected_registration_frame start entry_taint before tb` mp_tac >>
            simp[NoAsms, selected_registration_frame_def]) >>
         qpat_assum `selected_registration_resources unit.cu_context fn ARB 0 checks hit`
           (map_every assume_tac o CONJUNCTS o REWRITE_RULE [selected_registration_resources_def]) >>
         mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `m` |-> `min_calldata_size common.ec_env pref 0`,
                         `pay` |-> `common.ec_payable`, `st` |-> `checks`, `last` |-> `init`,
                         `s` |-> `hit`, `lo` |-> `0`, `PG` |-> `[]`, `G` |-> `Gh`, `tn` |-> `th`]
                   (SPEC_ALL entryChecksRejectJointTheory.compile_entry_checks_reject_joint)) >>
         (impl_tac >-
           (qpat_assum `hit.vs_call_ctx = _` (fn eq => simp[NoAsms, eq]) >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
            >- (qpat_assum `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp hit /\ _`
                  mp_tac >> simp[NoAsms]) >>
            metis_tac[])) >>
         disch_then (qx_choosel_then [`z`,`J`,`tz`] strip_assume_tac) >>
         qexistsl_tac [`z`,`J`,`tz`] >> conj_tac >- first_assum ACCEPT_TAC >>
         qx_gen_tac `D` >>
         irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> qexistsl_tac [`Gb`,`before`,`tb`] >>
         conj_tac >- first_assum (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC) >>
         irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> qexistsl_tac [`Gh`,`hit`,`th`] >>
         conj_tac >> first_assum (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC)) >>
      `?z J tz marks. z.vs_returndata = [] /\
         !D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
           (start,FEMPTY,entry_taint) marks (Abort Revert_abort z,J,tz)` suffices_by
        (disch_then (qx_choosel_then [`z`,`J`,`tz`,`marks`] strip_assume_tac) >>
         qexistsl_tac [`fn`,`z`,`J`,`tz`,`marks`] >> asm_rewrite_tac[]) >>
      reverse (Cases_on `LENGTH cd < 4 + SUM (MAP tv_abi_size tvs) \/
        calldata_decode_args cd kw_tvs (SUM (MAP tv_abi_size pos_tvs)) = NONE`)
      >- (
      `calldata_decode_args cd tvs 0 = NONE` by
        (qpat_assum `LENGTH cd < _ \/ calldata_decode_args cd tvs 0 = NONE`
           strip_assume_tac >> simp[] >>
         qpat_assum `~(LENGTH cd < _ \/ _)` mp_tac >> simp[]) >>
      `?kw_vals. calldata_decode_args cd kw_tvs
          (SUM (MAP tv_abi_size pos_tvs)) = SOME kw_vals` by
        (qpat_assum `~(LENGTH cd < _ \/ _)`
           (strip_assume_tac o PURE_REWRITE_RULE [DE_MORGAN_THM]) >>
         qpat_assum `~(calldata_decode_args cd kw_tvs _ = NONE)` mp_tac >>
         Cases_on `calldata_decode_args cd kw_tvs (SUM (MAP tv_abi_size pos_tvs))` >>
         pure_rewrite_tac[optionTheory.NOT_SOME_NONE] >> simp[NoAsms]) >>
      `calldata_decode_args cd pos_tvs 0 = NONE` by
        (Cases_on `calldata_decode_args cd pos_tvs 0` >> simp[] >>
         `!pos kw data off pv kv.
           calldata_decode_args data pos off = SOME pv /\
           calldata_decode_args data kw (off + SUM (MAP tv_abi_size pos)) = SOME kv ==>
           calldata_decode_args data (pos ++ kw) off = SOME (pv ++ kv)` by
           (rpt (pop_assum kall_tac) >>
            Induct >- simp[calldata_decode_args_def] >>
            rpt gen_tac >> simp[calldata_decode_args_def, LET_THM, AllCaseEqs()] >>
            strip_tac >> gvs[] >>
            `off + (SUM (MAP tv_abi_size pos) + tv_abi_size h) =
             off + tv_abi_size h + SUM (MAP tv_abi_size pos)` by decide_tac >>
            gvs[] >> first_x_assum drule_all >> simp[]) >>
         `pos_tvs ++ kw_tvs = tvs` by simp[Abbr `pos_tvs`, Abbr `kw_tvs`, TAKE_DROP] >>
         qpat_x_assum `!pos kw data off pv kv. _` (qspecl_then [`pos_tvs`,`kw_tvs`,`cd`,`0`] mp_tac) >>
         simp[]) >>
      `4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd` by
        (qpat_assum `~(LENGTH cd < _ \/ _)` mp_tac >>
         simp[NoAsms, arithmeticTheory.NOT_LESS]) >>
      (Q.SUBGOAL_THEN
        `min_calldata_size common.ec_env pref 0 <= 4 \/
         min_calldata_size common.ec_env pref 0 <= LENGTH start.vs_call_ctx.cc_calldata`
        assume_tac >-
        (disj2_tac >>
         qpat_assum `4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd` mp_tac >>
         qpat_assum `min_calldata_size common.ec_env pref 0 = _` (fn mc =>
           qpat_assum `start.vs_call_ctx = _` (fn cc => simp[NoAsms, mc, cc, Abbr `cd`])))) >>
      Cases_on `common.ec_payable \/ start.vs_call_ctx.cc_callvalue = 0w`
      >- (
        qunabbrev_tac `shadow_groups` >>
        drule_all groupedSelectedDefaultTheory.grouped_selected_default_initializer_start >>
        disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
          (qx_choosel_then
            [`vars`,`alloc_start`,`alloc_end`,`checks`,`si`,`cut`,`last`,
             `dispatch_end`,`shadow_si`,`shadow_cut`,`v`,`Gv`,`tv`,`a`,`Ga`,`ta`]
            (map_every assume_tac o CONJUNCTS))) >>
        `a.vs_call_ctx = start.vs_call_ctx` by
          (qpat_assum `selected_registration_frame start entry_taint a ta`
             (fn fr => mp_tac fr >> simp[NoAsms, selectedAcceptedFoldTheory.selected_registration_frame_def])) >>
        `a.vs_call_ctx.cc_calldata = cd` by
          (qpat_assum `a.vs_call_ctx = _` (fn ac =>
             qpat_assum `start.vs_call_ctx = _` (fn sc => simp[NoAsms, ac, sc, Abbr `cd`]))) >>
        `4 + SUM (MAP tv_abi_size tvs) <= LENGTH a.vs_call_ctx.cc_calldata` by
          (qpat_assum `a.vs_call_ctx.cc_calldata = cd` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        `LENGTH a.vs_call_ctx.cc_calldata < dimword (:256)` by
          (qpat_assum `a.vs_call_ctx = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        `calldata_decode_args a.vs_call_ctx.cc_calldata (DROP npos tvs)
           (SUM (MAP tv_abi_size (TAKE npos tvs))) <> NONE` by
          (qpat_assum `a.vs_call_ctx.cc_calldata = cd` SUBST1_TAC >>
           qpat_assum `calldata_decode_args cd kw_tvs _ = SOME _` mp_tac >>
           simp[NoAsms, Abbr `kw_tvs`, Abbr `pos_tvs`]) >>
        `npos = LENGTH args - LENGTH ds` by
          (qpat_assum `LENGTH ds = LENGTH dflts` (fn len => simp[NoAsms, len, Abbr `npos`])) >>
        `k <= LENGTH ds` by
          (qpat_assum `MEM (pref,k) (abi_entries args ds)` mp_tac >> simp[NoAsms, abi_entries_member]) >>
        `tvs = TAKE (npos+k) all_tvs` by simp[NoAsms, Abbr `tvs`] >>
        `LIST_REL (\(nm,ty) tv. abi_decoder_coherent common.ec_env tenv
                     common.ec_env.ce_struct_fields ty tv) args all_tvs` by
          (qpat_assum `LIST_REL (\arg tv. abi_decoder_coherent _ _ _ (SND arg) tv) args all_tvs` mp_tac >>
           ho_match_mp_tac LIST_REL_mono >> Cases >> simp[NoAsms]) >>
        `specs = MAP (\((nm,ty),e). (nm,ty,e)) (ZIP (DROP npos args,ds))` by
          (qpat_assum `npos = LENGTH args - LENGTH ds` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        `!nm op ty e. MEM (nm,op,ty,e) vars ==>
           ?id q b. op = Var q /\ not_fresh_at si q /\ lookup_var q a = SOME (n2w b) /\
             MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q])
               (fn_insts fn) /\
             FLOOKUP a.vs_allocas id = SOME (b,type_memory_bytes common.ec_env ty) /\
             b + type_memory_bytes common.ec_env ty < dimword (:256) /\ id < si.cs_next_id /\
             ptr_covers Ga ta q a (type_memory_bytes common.ec_env ty)` by
          (qpat_assum `!nm op ty e. MEM (_,_,_,_) vars ==> ?id q b. _` mp_tac >>
           rpt (pop_assum kall_tac) >> metis_tac[]) >>
        drule_all groupedRejectSuppliedArgumentsTheory.row22_supplied_suffix_start >>
        disch_then (qx_choosel_then [`residual`,`shadow_residual`,`u`,`Gu`,`tu`,`slots`,`vals`]
          (map_every assume_tac o CONJUNCTS)) >>
        `!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
           (start,FEMPTY,entry_taint) [] (OK u,Gu,tu)` by
          (gen_tac >>
           qpat_assum `!D explicit. gas_origin_ptr_path _ (start,_,_) [] (OK a,Ga,ta)`
             (qspecl_then [`D`,`EMPTY`]
               (irule o REWRITE_RULE [APPEND] o MATCH_MP gas_origin_ptr_path_append)) >>
           simp[NoAsms] >>
           qpat_assum `!D explicit. gas_origin_ptr_path _ (a,Ga,ta) [] (OK u,Gu,tu)`
             (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC)) >>
        qabbrev_tac `seed = u with vs_outcomes := []` >>
        `!i. active_inst fn i seed ==>
             raw_reachable (vs with vs_outcomes := []) unit.cu_context fn i seed` by
          (rpt strip_tac >>
           `active_inst fn i u` by
             (qpat_assum `active_inst fn i seed` mp_tac >>
              simp[NoAsms, Abbr `seed`, contextCodegenRelTheory.active_inst_def]) >>
           `gas_path unit.cu_context fn start 0 (OK u)` by
             (qpat_assum `!D. gas_origin_ptr_path _ (start,_,_) [] (OK u,Gu,tu)`
                (qspec_then `ARB`
                  (mp_tac o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_erase)) >>
              simp[NoAsms]) >>
           `raw_reachable vs unit.cu_context fn i u` by
             (mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `n` |-> `0`,
                `s` |-> `start`, `w` |-> `u`, `inst` |-> `i`]
                  callRejectMemoryTheory.raw_reachable_from_entry_path) >>
              impl_tac >-
                (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[Abbr `start`]) >>
              disch_then ACCEPT_TAC) >>
           `u.vs_requests = vs.vs_requests` by
             (qpat_assum `selected_registration_frame a ta u tu` mp_tac >>
              qpat_assum `selected_registration_frame start entry_taint a ta` mp_tac >>
              simp[NoAsms, selected_registration_frame_def, Abbr `start`]) >>
           `EVERY wf_function unit.cu_context.ctx_functions` by
             (qpat_assum `lowering_context_ok unit.cu_context` mp_tac >>
              simp[NoAsms, lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM]) >>
           mp_tac (Q.INST [`C` |-> `unit.cu_context`, `s` |-> `u`,
             `k` |-> `LENGTH vs.vs_requests`]
               requestCutOracleClipTheory.raw_reachable_outcome_clip) >>
           impl_tac >-
             (qpat_assum `u.vs_requests = vs.vs_requests` (fn rq =>
                simp[NoAsms, rq, extCallOracleTheory.record_request_def]) >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
           qpat_assum `u.vs_requests = vs.vs_requests` (fn rq =>
             simp[NoAsms, rq, Abbr `seed`])) >>
        `!callee inst w. frag_reachable unit.cu_context fn seed callee inst w ==>
           dalloca_fmp_headroom inst w` by
          (Cases_on `ctx_has_dalloca unit.cu_context`
           >- (rpt gen_tac >> strip_tac >>
               qpat_assum `ctx_has_dalloca unit.cu_context ==>
                  !fn inst s. raw_reachable (vs with vs_outcomes := []) _ fn inst s ==> _`
                 (drule_then irule) >>
               qexists_tac `callee` >>
               qpat_assum `frag_reachable unit.cu_context fn seed callee inst w`
                 (qspec_then `vs with vs_outcomes := []` MATCH_MP_TAC o
                  MATCH_MP (Q.SPECL [`unit.cu_context`,`fn`,`seed`,`callee`,`inst`,`w`]
                    deployBodyReachabilityTheory.raw_reachable_through_fragment)) >>
               first_assum ACCEPT_TAC) >>
           rpt gen_tac >> strip_tac >>
           `MEM fn unit.cu_context.ctx_functions` by
             (irule lookup_function_MEM >> qexists_tac `"__entry"` >> first_assum ACCEPT_TAC) >>
           drule_all contextRawReachableTheory.frag_reachable_members >> strip_tac >>
           qpat_assum `~ctx_has_dalloca unit.cu_context` mp_tac >>
           simp[NoAsms, ctx_has_dalloca_def, EXISTS_MEM,
             unitTransformDefsTheory.dalloca_fmp_headroom_def] >>
           disch_then (qspec_then `callee` mp_tac) >>
           qpat_assum `MEM callee unit.cu_context.ctx_functions`
             (fn mem => simp[NoAsms, mem]) >>
           disch_then (qspec_then `inst` mp_tac) >>
           qpat_assum `MEM inst (fn_insts callee)` (fn mem => simp[NoAsms, mem])) >>
        qabbrev_tac `kept = MAP (\((aid,p,base,tv),v). (aid,p,base,tv,v)) (ZIP (TAKE k slots,vals))` >>
        `LENGTH (TAKE k slots) = LENGTH vals` by
          (qpat_assum `LIST_REL _ (TAKE k slots) vals` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
           simp[NoAsms]) >>
        `MAP FST kept = MAP FST (TAKE k slots)` by
          (qpat_assum `LENGTH (TAKE k slots) = LENGTH vals` (fn len =>
             simp[NoAsms, Abbr `kept`, Once LIST_EQ_REWRITE, LENGTH_ZIP, EL_MAP, EL_ZIP, len]) >>
           rpt strip_tac >> qabbrev_tac `slot = EL x (TAKE k slots)` >>
           PairCases_on `slot` >> simp[NoAsms]) >>
        `ALL_DISTINCT (MAP FST (DROP k slots) ++ MAP FST kept)` by
          (`ALL_DISTINCT (MAP FST (TAKE k slots) ++ MAP FST (DROP k slots))` by
             (pure_once_rewrite_tac [GSYM MAP_APPEND] >>
              pure_rewrite_tac [TAKE_DROP] >> first_assum ACCEPT_TAC) >>
           qpat_assum `ALL_DISTINCT (_ ++ _)` mp_tac >>
           qpat_assum `MAP FST kept = _` (fn fst_kept =>
             simp[NoAsms, fst_kept, ALL_DISTINCT_APPEND']) >>
           rpt (pop_assum kall_tac) >> metis_tac[DISJOINT_SYM]) >>
        `EVERY (^row22_kw_alloc residual seed Gu tu) (DROP k slots)` by
          (qpat_assum `EVERY _ (DROP k slots)` mp_tac >>
           simp[NoAsms, Abbr `seed`, bodyPtrDefsTheory.ptr_covers_def,
             loweringBudgetFrameOracleTransportTheory.lookup_var_outcomes_update]) >>
        `EVERY (^row22_kw_initialized residual seed Gu tu) kept` by
          (qpat_assum `LIST_REL _ (TAKE k slots) vals` mp_tac >>
           simp[NoAsms, Abbr `seed`, Abbr `kept`, LIST_REL_EVERY_ZIP, EVERY_MAP,
                EVERY_MEM, FORALL_PROD, bodyPtrDefsTheory.ptr_covers_def,
                loweringBudgetFrameOracleTransportTheory.lookup_var_outcomes_update] >>
           disch_then (ACCEPT_TAC o CONJUNCT2)) >>
        qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts
                                     (tx with function_name := name) src` >>
        qabbrev_tac `env = artifact_env art mods src` >>
        qabbrev_tac `ce0 = common.ec_env with ce_vars := FEMPTY` >>
        qpat_assum `source_deployment_rel_mods mods exps am tx`
          (map_every assume_tac o CONJUNCTS o REWRITE_RULE [source_deployment_rel_mods_def]) >>
        `ALOOKUP cx.sources cx.txn.target = SOME mods` by
          (qpat_assum `ALOOKUP am.sources tx.target = SOME mods` (fn mods_at =>
             simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, mods_at])) >>
        `check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art` by
          (qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
             simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, checked])) >>
        `linked_fn_sigs_declared mods cx env.fn_sigs` by
          (simp[NoAsms, Abbr `env`, artifact_env_def, frame_maps_def] >>
           drule_then ACCEPT_TAC bodyCallSupportTheory.check_contract_linked_fn_sigs_declared) >>
        qabbrev_tac `base_env = build_compile_env_unit mods src External mut name args ret code T` >>
        `contract_inv mods exps unit.cu_context
           (base_env with ce_target := rpolicy.rpol_target) cx` by
          (qunabbrev_tac `base_env` >> irule checked_linked_contract_inv >>
           simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, IS_SOME_EQ_NOT_NONE] >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
           FIRST [qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
                    simp[NoAsms, checked] >> NO_TAC),
                  qexistsl_tac [`am`,`tx`] >> simp[NoAsms] >> first_assum ACCEPT_TAC]) >>
        `common.ec_env =
           (update_cenv_nonreentrant
             (if ret = NoneT then base_env with ce_raw_return := rr
              else update_cenv_ret_abi (base_env with ce_raw_return := rr) ret)
             nr global_nonreentrant_slot T (mut = View))
           with ce_target := rpolicy.rpol_target` by
          (qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _` mp_tac >>
           Cases_on `ret = NoneT` >>
           pop_assum (fn rval => qpat_assum `ds <> []` (fn defaults =>
             simp[NoAsms, rval, defaults, Abbr `base_env`, package_external_group_unit_def,
               package_external_fn_unit_def, set_external_package_target_def, NULL_EQ, LET_THM])) >>
           strip_tac >>
           qpat_assum `<|ec_env := _; ec_pos_args := _; ec_common_label := _;
                         ec_nonreentrant := _; ec_nkey := _; ec_transient := _;
                         ec_view := _; ec_payable := _; ec_body := _; ec_return := _|> = common`
             (mp_tac o Q.AP_TERM `\c. c.ec_env`) >>
           simp[NoAsms] >> disch_then (ACCEPT_TAC o SYM)) >>
        `ce0.ce_func_return_type = build_func_return_type_mods mods` by
          (qpat_assum `contract_inv mods exps _ (base_env with ce_target := _) cx`
            (mp_tac o MATCH_MP bodyInvExecutionPropsTheory.contract_inv_return_types) >>
           qpat_assum `common.ec_env = _` (fn installed =>
             Cases_on `ret = NoneT` >> pop_assum (fn rval =>
             simp[NoAsms, rval, Abbr `ce0`, installed,
               update_cenv_nonreentrant_def, update_cenv_ret_abi_def]))) >>
        `contract_namespaces_ok F mods` by
          (qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
             (ACCEPT_TAC o MATCH_MP vyperTypeContractContextTheory.check_contract_namespaces_ok)) >>
        `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
            ce0.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
          (qpat_assum `ce0.ce_func_return_type = _` (fn tab => pure_rewrite_tac [tab]) >>
           Cases >> rpt gen_tac >> strip_tac >>
           rename1 `FLOOKUP env.fn_sigs (owner,fname) = SOME sg` >>
           `FLOOKUP art.cta_fn_sigs (owner,fname) = SOME sg` by
             (qpat_assum `FLOOKUP env.fn_sigs (owner,fname) = SOME sg` mp_tac >>
              simp[NoAsms, Abbr `env`, artifact_env_def, frame_maps_def]) >>
           `FLOOKUP (build_contract_type_artifact F mods).cta_fn_sigs
               (owner,fname) = SOME sg` by
             (qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
                (assume_tac o MATCH_MP vyperTypeContractStaticMapsTheory.check_contract_artifact_fields) >>
              qpat_x_assum `contract_namespaces_ok F mods /\ _`
                (map_every assume_tac o CONJUNCTS) >>
              qpat_assum `FLOOKUP art.cta_fn_sigs (owner,fname) = SOME sg` mp_tac >>
              qpat_assum `art.cta_fn_sigs = _` (fn sigs =>
                simp[NoAsms, sigs, vyperTypeContractStaticMapsTheory.FLOOKUP_DRESTRICT_SOME])) >>
           drule_all vyperTypeContractStaticMapsTheory.build_contract_type_artifact_fn_sigs_declared_sound >>
           simp[NoAsms, include_fn_sig_def] >>
           disch_then (qx_choosel_then [`owner_tops`,`vis`,`fm`,`guard`,`raw`,`params`,`defs`,`stmts`]
             (map_every assume_tac o CONJUNCTS)) >>
           `vis <> External` by
             (qpat_assum `include_fn_sig F vis` mp_tac >> Cases_on `vis` >>
              simp[NoAsms, include_fn_sig_def]) >>
           `(base_env with ce_target := rpolicy.rpol_target).ce_func_return_type
                (nsid_to_string (owner,fname)) = sg.ret_ty` by
             (irule linked_entry_declared_return_type >>
              qexistsl_tac [`params`,`stmts`,`unit.cu_context`,`cx`,`defs`,`exps`,
                            `mods`,`fm`,`guard`,`raw`,`owner_tops`,`vis`] >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
           qpat_assum `contract_inv mods exps _ (base_env with ce_target := _) cx`
             (fn inv => qpat_assum `(base_env with ce_target := _).ce_func_return_type _ = _`
               (ACCEPT_TAC o REWRITE_RULE [MATCH_MP bodyInvExecutionPropsTheory.contract_inv_return_types inv]))) >>
        `ce0.ce_flag_member_id =
           (base_env with ce_target := rpolicy.rpol_target).ce_flag_member_id` by
          (qpat_assum `common.ec_env = _` (fn installed =>
             Cases_on `ret = NoneT` >> pop_assum (fn rval =>
             simp[NoAsms, rval, Abbr `ce0`, installed,
               update_cenv_nonreentrant_def, update_cenv_ret_abi_def]))) >>
        `!owner fid ts members member index.
           get_module_code cx owner = SOME ts /\ lookup_flag fid ts = SOME members /\
           INDEX_OF member members = SOME index ==>
           ce0.ce_flag_member_id (nsid_to_string (owner,fid)) member = index` by
          (qpat_assum `ce0.ce_flag_member_id = _` (fn tab => pure_rewrite_tac [tab]) >>
           rpt gen_tac >> strip_tac >> irule linked_entry_flag_member_id >>
           qexistsl_tac [`unit.cu_context`,`cx`,`F`,`exps`,`members`,`mods`,`ts`] >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `checked_contract_runtime_ready art mods am tx /\
         machine_well_typed am /\ call_tx_well_typed tx` by
          (drule_all source_typing_ok_runtime_ready_mods >>
           qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
             simp[NoAsms, checked])) >>
        `context_well_typed cx` by
          (qpat_assum `call_tx_well_typed tx` mp_tac >>
           simp[NoAsms, Abbr `cx`, initial_evaluation_context_def,
             context_well_typed_def, call_tx_well_typed_def]) >>
        qabbrev_tac `es_in = initial_state am [FEMPTY] with <|outcomes := SOME []; requests := []|>` >>
        `value_transfer_ok cx.txn es_in.accounts /\
         start.vs_call_ctx.cc_callvalue = n2w cx.txn.value` by
          (qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
           qpat_assum `start.vs_call_ctx = vs.vs_call_ctx` (fn cc =>
             simp[NoAsms, cc, Abbr `cx`, Abbr `es_in`, initial_evaluation_context_def,
               initial_venom_state_rel_mods_def, initial_state_def,
               venom_env_rel_def, call_ctx_rel_def, e2eDefsTheory.value_transfer_ok_def])) >>
        `?es. send_call_value mut cx es_in = (INL (),es)` by
          (Cases_on `send_call_value mut cx es_in` >> Cases_on `q`
           >- (Cases_on `x` >> simp[NoAsms]) >>
           drule_all send_call_value_reject_condition >> strip_tac >>
           `cx.txn.value < dimword (:256)` by
             (qpat_assum `context_well_typed cx` mp_tac >>
              simp[NoAsms, context_well_typed_def, dimword_def]) >>
           `start.vs_call_ctx.cc_callvalue <> 0w` by
             (qpat_assum `start.vs_call_ctx.cc_callvalue = _` SUBST1_TAC >>
              qpat_assum `cx.txn.value < dimword (:256)` (fn lt =>
              qpat_assum `cx.txn.value <> 0` (fn nz =>
                simp[NoAsms, n2w_11, LESS_MOD, lt, nz]))) >>
           qpat_assum `common.ec_payable \/ _` mp_tac >>
           qpat_assum `common.ec_payable <=> _` (fn pay =>
             qpat_assum `mut <> Payable` (fn mu =>
               qpat_assum `start.vs_call_ctx.cc_callvalue <> 0w` (fn nz =>
                 simp[NoAsms, pay, mu, nz])))) >>
        `es.scopes = [FEMPTY] /\ es.immutables = am.immutables /\
         es.storage_trace = [] /\ es.gas_obs = [] /\ es.outcomes = SOME [] /\ es.requests = []` by
          (qpat_assum `send_call_value mut cx es_in = (INL (),es)`
             (mp_tac o MATCH_MP external_send_call_value_frame) >>
           simp[NoAsms, Abbr `es_in`, initial_state_def, vyperStateTheory.evaluation_state_component_equality]) >>
        `accounts_well_typed es.accounts` by
          (irule send_call_value_accounts_well_typed_c53 >>
           qexistsl_tac [`cx`,`mut`,`INL ()`,`es_in`] >>
           reverse conj_tac >- first_assum ACCEPT_TAC >>
           qpat_assum `machine_well_typed am` mp_tac >>
           simp[NoAsms, Abbr `es_in`, initial_state_def, vyperTypeInitialStateTheory.machine_well_typed_def]) >>
        `state_well_typed es` by
          (qpat_assum `es.scopes = _` (fn scopes =>
           qpat_assum `es.immutables = _` (fn imms =>
             simp[NoAsms, state_well_typed_def, scopes, imms, scope_well_typed_def])) >>
           qpat_assum `machine_well_typed am` mp_tac >>
           simp[NoAsms, vyperTypeInitialStateTheory.machine_well_typed_def]) >>
        `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx es.immutables` by
          (`immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
              (initial_evaluation_context am.sources am.layouts tx NONE) am.immutables` by
             (qpat_assum `checked_contract_runtime_ready art mods am tx` mp_tac >>
              simp[NoAsms, checked_contract_runtime_ready_def]) >>
           pop_assum mp_tac >>
           qpat_assum `es.immutables = _` (fn imms =>
             simp[NoAsms, imms, Abbr `cx`, vyperTypeInitialStateTheory.immutables_ready_def,
                  initial_evaluation_context_def, vyperContextTheory.get_module_code_def,
                  vyperContextTheory.get_tenv_def]) >>
           strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `env_consistent env cx es /\ functions_well_typed cx` by
          (`es with scopes := [FEMPTY] = es` by
             (qpat_assum `es.scopes = _` (fn scopes =>
                simp[NoAsms, vyperStateTheory.evaluation_state_component_equality, scopes])) >>
           `env_consistent (artifact_env art mods src) cx (es with scopes := [FEMPTY]) /\
            state_well_typed (es with scopes := [FEMPTY]) /\ functions_well_typed cx` by
             (irule vyperTypeExternalDefaultsTheory.checked_external_empty_frame_ready >>
              rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              qexistsl [`am`, `tx with function_name := name`] >>
              simp[NoAsms, Abbr `cx`] >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
           qpat_assum `env_consistent (artifact_env art mods src) cx _` mp_tac >>
           qpat_assum `es with scopes := [FEMPTY] = es` (fn frame_eq =>
             simp[NoAsms, frame_eq, Abbr `env`]) >>
           disch_tac >> first_assum ACCEPT_TAC) >>
        `body_const_cells_agree_mods mods cx env es` by
          (`env.type_defs = get_tenv cx` by
             (drule vyperTypeConstantFoldTheory.get_tenv_sources >>
              simp[NoAsms, Abbr `env`, artifact_env_def]) >>
           `EVERY (no_sha256_expr o SND) (consts_env_mods mods) /\
            EVERY (no_neg_exp_expr o SND) (consts_env_mods mods)` by
             (qpat_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
              qpat_assum `classify_functions_unit _ _ = _` (fn cls =>
                simp[NoAsms, lower_vyper_runtime_unit_mods_def, cls, AllCaseEqs()]) >>
              strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
           irule checked_body_const_cells_agree_mods >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
           >- (qexists `account_immutables am tx.target` >>
               conj_tac
               >- (qpat_assum `source_typing_ok_mods mods exps am tx` mp_tac >>
                   simp[NoAsms, source_typing_ok_mods_def] >> strip_tac >>
                   first_assum ACCEPT_TAC) >>
               qpat_assum `es.immutables = _` (fn imms =>
                 simp[NoAsms, imms, e2eDefsTheory.account_immutables_def,
                      Abbr `cx`, initial_evaluation_context_def])) >>
           qexists `art` >> simp[NoAsms, frame_maps_def, Abbr `env`, artifact_env_def] >>
           first_assum ACCEPT_TAC) >>
        `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==>
                 vyperSubscriptOverlap$accesses_expr r = []` by
          (PairCases >> gen_tac >> disch_tac >>
           qpat_assum `body_const_cells_agree_mods mods cx env es`
             (strip_assume_tac o REWRITE_RULE [bodyFullPredsModsTheory.body_const_cells_agree_mods_def]) >>
           qpat_assum `!src id r. ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==> _`
             drule >> strip_tac >> first_assum ACCEPT_TAC) >>
        `MEM (src,name) (linked_live_functions mods exps)` by
          (pure_rewrite_tac [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
           CONV_TAC (DEPTH_CONV BETA_CONV) >> irule (CONJUNCT1 vyperTypeCallGraphSoundnessTheory.call_closure_from_roots) >>
           simp[NoAsms, MEM_APPEND, Abbr `src`] >> Cases_on `ALOOKUP exps name`
           >- (disj1_tac >>
               qpat_assum `ALOOKUP mods NONE = SOME src_tops` (fn eq =>
                 simp[NoAsms, linked_main_roots_def, eq, contract_keys_def, MEM_APPEND]) >>
               disj1_tac >> simp[NoAsms, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
               qexists `FunctionDecl External mut nr rr name args dflts ret rawbody` >>
               simp[NoAsms, external_name_keys_toplevel_def] >> first_assum ACCEPT_TAC) >>
           disj2_tac >> simp[NoAsms, linked_export_roots_def, MEM_MAP] >>
           qexists `(name,x)` >> simp[NoAsms] >> irule alistTheory.ALOOKUP_MEM >>
           first_assum ACCEPT_TAC) >>
        `check_linked_state_ownership am.layouts tx.target mods (linked_live_functions mods exps)` by
          (drule_all check_contract_linked_state_ownership_ok >>
           simp[NoAsms, linked_state_ownership_ok_def]) >>
        `immutable_section_layout_mods mods ce0` by
          (`ce0.ce_module_vars = (base_env with ce_target := rpolicy.rpol_target).ce_module_vars` by
             (qpat_assum `common.ec_env = _` (fn installed =>
                Cases_on `ret = NoneT` >> pop_assum (fn rval =>
                simp[NoAsms, rval, Abbr `ce0`, installed,
                     update_cenv_nonreentrant_def, update_cenv_ret_abi_def]))) >>
           qpat_assum `contract_inv mods exps _ (base_env with ce_target := _) cx`
             (mp_tac o MATCH_MP bodyInvSplitTheory.contract_inv_immutable_section_layout) >>
           qpat_assum `ce0.ce_module_vars = _` (fn eq =>
             pure_rewrite_tac [bodyInvSplitTheory.immutable_section_layout_mods_def, eq]) >>
           disch_tac >> first_assum ACCEPT_TAC) >>
        `!p P. (!z. p z ==> ?ty key. z = TopLevelName ty key /\ P key) ==>
          !e. MEM e ds /\ supported_expr_exists p e ==>
              ?key. P key /\ ALOOKUP (consts_env_mods mods) key = NONE /\
                MEM (ReadAcc (StateRef key)) (accesses_exprs dflts)` by
          (rpt gen_tac >> disch_tac >>
           qabbrev_tac `E = consts_env_mods mods` >>
           `!z. accesses_expr z = [] ==> ~supported_expr_exists p z` by
             (`(!z. supported_expr_exists p z ==>
                 ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_expr z)) /\
               (!t. supported_target_exists p t ==>
                 ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_target t)) /\
               (!xs. supported_exprs_exists p xs ==>
                 ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_exprs xs)) /\
               (!opt. supported_opt_exists p opt ==>
                 ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_opt opt)) /\
               (!fields. supported_fields_exists p fields ==>
                 ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_named_exprs fields))` by
                (qpat_assum `!z. p z ==> _` mp_tac >>
                 rpt (pop_assum kall_tac) >> disch_tac >>
                 ho_match_mp_tac accesses_expr_ind >>
                 simp[supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
                 rpt strip_tac >> res_tac >> fs[accesses_expr_def, MEM_APPEND] >> metis_tac[]) >>
              qpat_assum `!z. supported_expr_exists p z ==> _` mp_tac >>
              rpt (pop_assum kall_tac) >> metis_tac[MEM]) >>
           `(!z. supported_expr_exists p (subst_consts_expr_mods E z) ==>
                ?key. P key /\ ALOOKUP E key = NONE /\
                  MEM (ReadAcc (StateRef key)) (accesses_expr (subst_consts_expr_mods E z))) /\
            (!t. supported_target_exists p (subst_consts_btarget_mods E t) ==>
                ?key. P key /\ ALOOKUP E key = NONE /\
                  MEM (ReadAcc (StateRef key)) (accesses_target (subst_consts_btarget_mods E t))) /\
            (!xs. supported_exprs_exists p (subst_consts_exprs_mods E xs) ==>
                ?key. P key /\ ALOOKUP E key = NONE /\
                  MEM (ReadAcc (StateRef key)) (accesses_exprs (subst_consts_exprs_mods E xs))) /\
            (!opt. supported_opt_exists p (subst_consts_opt_mods E opt) ==>
                ?key. P key /\ ALOOKUP E key = NONE /\
                  MEM (ReadAcc (StateRef key)) (accesses_opt (subst_consts_opt_mods E opt))) /\
            (!fields. supported_fields_exists p (subst_consts_fields_mods E fields) ==>
                ?key. P key /\ ALOOKUP E key = NONE /\
                  MEM (ReadAcc (StateRef key)) (accesses_named_exprs (subst_consts_fields_mods E fields)))` by
             (qpat_assum `!z. p z ==> _` mp_tac >>
              qpat_assum `!key r. ALOOKUP E key = SOME r ==> _` mp_tac >>
              qpat_assum `!z. accesses_expr z = [] ==> _` mp_tac >>
              rpt (pop_assum kall_tac) >> rpt disch_tac >>
              ho_match_mp_tac accesses_expr_ind >>
              simp[subst_consts_expr_mods_def, supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
              rpt strip_tac >> res_tac >> gvs[]
              >~ [`subst_consts_expr_mods E (TopLevelName _ _)`]
              >- (rename1 `subst_consts_expr_mods E (TopLevelName ty nsid)` >>
                  PairCases_on `nsid` >> Cases_on `ALOOKUP E (nsid0,nsid1)` >>
                  gvs[subst_consts_expr_mods_def, accesses_expr_def, supported_expr_exists_def] >>
                  res_tac >> gvs[]) >>
              metis_tac[]) >>
           `!xs. supported_exprs_exists p xs <=> EXISTS (supported_expr_exists p) xs` by
             (Induct >> simp[NoAsms, supported_expr_exists_def] >>
              qpat_assum `supported_exprs_exists p _ <=> _` (fn ih => simp[NoAsms, ih])) >>
           rpt strip_tac >>
           `supported_exprs_exists p ds` by
             (qpat_assum `!xs. supported_exprs_exists p xs <=> _` (fn eq =>
                pure_rewrite_tac[eq, EXISTS_MEM]) >>
              qexists `e` >> conj_tac >> first_assum ACCEPT_TAC) >>
           qpat_assum `!xs. supported_exprs_exists p (subst_consts_exprs_mods E xs) ==> _`
             (qspec_then `dflts` mp_tac) >>
           (impl_tac >- (qpat_assum `Abbrev (ds = _)`
              (PURE_ONCE_REWRITE_TAC o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
              first_assum ACCEPT_TAC)) >>
           disch_then (qx_choose_then `read_key` strip_assume_tac) >>
           qexists `read_key` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
           qpat_assum `!key r. ALOOKUP E key = SOME r ==> _`
             (strip_assume_tac o MATCH_MP linked_subst_accesses_subset) >>
           qpat_assum `!xs a. MEM a (accesses_exprs (subst_consts_exprs_mods E xs)) ==> _`
             (qspecl_then [`dflts`,`ReadAcc (StateRef read_key)`] irule) >>
           first_assum ACCEPT_TAC) >>
        `!isrc ts v init id ty sl.
           ALOOKUP mods isrc = SOME ts /\ MEM (VariableDecl v (Constant init) id ty sl) ts ==>
           ALOOKUP (consts_env_mods mods) (isrc,id) <> NONE` by
          (`!s ts E key. MEM key (MAP FST E) \/
              (?v init id ty sl. key = (s,id) /\ MEM (VariableDecl v (Constant init) id ty sl) ts) ==>
            MEM key (MAP FST (module_consts_env_mods s ts E))` by
             (rpt (pop_assum kall_tac) >> ho_match_mp_tac module_consts_env_mods_ind >>
              simp[module_consts_env_mods_def, MEM_APPEND] >> metis_tac[]) >>
           `!ms E key. MEM key (MAP FST E) \/
              (?s ts v init id ty sl. key = (s,id) /\ MEM (s,ts) ms /\
                  MEM (VariableDecl v (Constant init) id ty sl) ts) ==>
            MEM key (MAP FST (consts_env_mods_acc ms E))` by
             (pop_assum mp_tac >> rpt (pop_assum kall_tac) >> disch_tac >>
              Induct >> simp[consts_env_mods_acc_def, FORALL_PROD] >>
              rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
           map_every qx_gen_tac [`isrc`,`ts`,`cv`,`init`,`id`,`ty`,`sl`] >> rpt strip_tac >>
           `MEM (isrc,id) (MAP FST (consts_env_mods mods))` by
             (simp[NoAsms, consts_env_mods_def, consts_env_modules_order_eq] >>
              first_x_assum irule >> simp[NoAsms, MEM_constants_order] >>
              drule ALOOKUP_MEM >> strip_tac >>
              qexistsl [`ts`,`cv`,`init`,`ty`,`sl`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
           qpat_assum `ALOOKUP (consts_env_mods mods) (isrc,id) = NONE` mp_tac >>
           qpat_assum `MEM (isrc,id) _` (fn mem => simp[NoAsms, ALOOKUP_NONE, mem])) >>
        `!ts acc id. MEM id (MAP FST (module_consts_env ts acc)) ==>
           MEM id (MAP FST acc) \/ ?v c ty sl. MEM (VariableDecl v (Constant c) id ty sl) ts` by
          (rpt (pop_assum kall_tac) >> recInduct constSubstTheory.module_consts_env_ind >> rw[constSubstTheory.module_consts_env_def] >>
           res_tac >> gvs[] >> metis_tac[]) >>
        `!read_key. MEM (ReadAcc (StateRef read_key)) (accesses_exprs dflts) ==>
           ((?its. mods = [(NONE,its)]) \/
             linked_state_ref_allocated am.layouts tx.target mods read_key)` by
          (gen_tac >> disch_tac >>
           qpat_assum `check_linked_state_ownership _ _ _ _` mp_tac >>
           pure_rewrite_tac[check_linked_state_ownership_def] >>
           disch_then (DISJ_CASES_THEN2 mp_tac assume_tac)
           >- (Cases_on `mods` >> simp[NoAsms] >> PairCases_on `h` >>
               Cases_on `h0` >> Cases_on `t` >> simp[NoAsms]) >>
           `MEM (src,src_tops) mods` by (irule ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
           qpat_assum `EVERY _ mods` (fn own =>
             qpat_assum `MEM (src,src_tops) mods` (mp_tac o MATCH_MP (REWRITE_RULE[EVERY_MEM] own))) >>
           simp[NoAsms, Once EVERY_MEM] >>
           qpat_assum `MEM (FunctionDecl External mut nr rr name args dflts ret rawbody) src_tops`
             (fn decl => disch_then (mp_tac o C MATCH_MP decl)) >>
           qpat_assum `MEM (src,name) (linked_live_functions mods exps)` (fn live => simp[NoAsms, live]) >>
           strip_tac >> disj2_tac >>
           qpat_assum `!a. MEM a (accesses_exprs dflts) \/ MEM a (accesses_stmts rawbody) ==> _`
             (qspec_then `ReadAcc (StateRef read_key)` mp_tac) >>
           qpat_assum `MEM (ReadAcc (StateRef read_key)) (accesses_exprs dflts)`
             (fn read => simp[NoAsms, MEM_APPEND, read])) >>
        `!e. MEM e (DROP k ds) ==>
             ~supported_expr_exists (const_name_root_mods mods) e /\
             ~supported_expr_exists (unallocated_bare_global_root ce0 env) e` by
          (gen_tac >> disch_tac >>
           `MEM e ds` by
             (qpat_assum `MEM e (DROP k ds)` (irule o MATCH_MP rich_listTheory.MEM_DROP_IMP)) >>
           conj_tac
           >- (strip_tac >>
               qpat_assum `!p P. (!z. p z ==> _) ==> _`
                 (qspecl_then [`const_name_root_mods mods`,`cx_const_name_mods mods`] mp_tac) >>
               (impl_tac >- (Cases >> simp[NoAsms, const_name_root_mods_def])) >>
               disch_then (qspec_then `e` mp_tac) >>
               (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
               disch_then (qx_choose_then `read_key` strip_assume_tac) >>
               PairCases_on `read_key` >>
               qpat_assum `cx_const_name_mods mods _`
                 (strip_assume_tac o REWRITE_RULE [cx_const_name_mods_def]) >>
               qpat_assum `!ts acc id. MEM id (MAP FST (module_consts_env ts acc)) ==> _`
                 drule >> simp[NoAsms] >> strip_tac >>
               qpat_assum `!isrc ts v init id ty sl. _ ==> ALOOKUP _ _ <> NONE` mp_tac >>
               qpat_assum `ALOOKUP mods read_key0 = SOME _` mp_tac >>
               qpat_assum `ALOOKUP (consts_env_mods mods) (read_key0,read_key1) = NONE` mp_tac >>
               rpt (pop_assum kall_tac) >> metis_tac[]) >>
           strip_tac >>
           qpat_assum `!p P. (!z. p z ==> _) ==> _`
             (qspecl_then [`unallocated_bare_global_root ce0 env`,
               `\rk. IS_SOME (FLOOKUP env.bare_globals rk) /\ FLOOKUP ce0.ce_module_vars rk = NONE`] mp_tac) >>
           BETA_TAC >>
           (impl_tac >- (Cases >> simp[NoAsms, unallocated_bare_global_root_def])) >>
           disch_then (qspec_then `e` mp_tac) >>
           (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
           disch_then (qx_choose_then `read_key` strip_assume_tac) >>
           PairCases_on `read_key` >>
           `?rty. FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals
                       (read_key0,read_key1) = SOME rty` by
             (qpat_assum `IS_SOME (FLOOKUP env.bare_globals _)` mp_tac >>
              qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
                (strip_assume_tac o MATCH_MP check_contract_nonsig_maps) >>
              qpat_assum `art.cta_bare_globals = _` (fn eq =>
                simp[NoAsms, Abbr `env`, artifact_env_def, eq, IS_SOME_EXISTS])) >>
           drule_all build_contract_type_artifact_bare_globals_sound >>
           disch_then (DISJ_CASES_THEN strip_assume_tac) >>
           qpat_x_assum `read_key1 = _` SUBST_ALL_TAC
           >- (qpat_assum `!read_key. MEM (ReadAcc (StateRef read_key)) (accesses_exprs dflts) ==> _`
                 (drule_then strip_assume_tac) >>
               rename1 `MEM (VariableDecl iv Immutable id_str rty isl) itops` >>
               `mods = [(NONE,itops)] \/
                  linked_state_ref_allocated am.layouts tx.target mods (read_key0,id_str)` by
                 (TRY (disj2_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
                  qpat_assum `ALOOKUP mods read_key0 = SOME itops` mp_tac >>
                  qpat_assum `mods = [(NONE,_)]` (fn eq => simp[NoAsms, eq, AllCaseEqs()])) >>
               `?imm_off. FLOOKUP ce0.ce_module_vars (read_key0,id_str) = SOME (ImmutableLoc imm_off)` by
                 (irule (INST_TYPE [``:'a`` |-> ``:160 word``, ``:'b`` |-> ``:num``]
                    linked_owned_immutable_location) >>
                  qexistsl [`tx.target`,`am.layouts`,`mods`,`isl`,`itops`,`rty`,`iv`] >>
                  rpt conj_tac >>
                  (first_assum ACCEPT_TAC ORELSE
                   (disj1_tac >> first_assum ACCEPT_TAC) ORELSE
                   (disj2_tac >> first_assum ACCEPT_TAC))) >>
               qpat_assum `FLOOKUP ce0.ce_module_vars (read_key0,id_str) = SOME _` mp_tac >>
               qpat_assum `FLOOKUP ce0.ce_module_vars (read_key0,id_str) = NONE`
                 (fn eq => simp[NoAsms, eq])) >>
           qpat_assum `!isrc ts v init id ty sl. _ ==> ALOOKUP _ _ <> NONE` mp_tac >>
           qpat_assum `ALOOKUP mods read_key0 = SOME _` mp_tac >>
           qpat_assum `ALOOKUP (consts_env_mods mods) (read_key0,id_str) = NONE` mp_tac >>
           qpat_assum `MEM (VariableDecl _ (Constant _) id_str _ _) _` mp_tac >>
           rpt (pop_assum kall_tac) >> metis_tac[]) >>
        `get_tenv cx = type_env_all_modules mods` by
          drule_then ACCEPT_TAC vyperTypeConstantFoldTheory.get_tenv_sources >>
        `env.type_defs = get_tenv cx` by
          (qpat_assum `get_tenv cx = _` (fn eq => simp[NoAsms, eq, Abbr `env`, artifact_env_def])) >>
        `call_evaluation_safe cx []` by
          (`cx with stk := [(src,name)] = cx` by
             simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
           pop_assum (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
           irule vyperTypeCallStackSoundnessTheory.checked_contract_call_evaluation_safe_singleton >>
           qexistsl [`art`,`cx.layouts`,`mods`] >>
           simp[NoAsms, vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_def] >>
           conj_tac >> first_assum ACCEPT_TAC) >>
        `!owner id vt. FLOOKUP art.cta_toplevel_vtypes (owner,id) = SOME vt ==>
           well_formed_vtype (type_env_all_modules mods) vt` by
          (mp_tac (Q.INST [`sources` |-> `am.sources`, `tx` |-> `tx`,
                      `addr` |-> `tx.target`, `layouts` |-> `am.layouts`]
                    (SPEC_ALL check_contract_toplevel_vtypes_consistent_initial)) >>
           qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
             qpat_assum `ALOOKUP am.sources tx.target = SOME mods` (fn codes =>
               simp[NoAsms, checked, codes])) >>
           strip_tac >> first_assum ACCEPT_TAC) >>
        `!sid ts vis m nr0 raw nm as0 ds0 rt ss.
          ALOOKUP mods sid = SOME ts /\ MEM (FunctionDecl vis m nr0 raw nm as0 ds0 rt ss) ts ==>
          stmts_loop_calls_ok mods (subst_consts_stmts_mods (consts_env_mods mods) ss)` by
          (rpt gen_tac >> strip_tac >> drule_then assume_tac ALOOKUP_MEM >>
           drule_all_then assume_tac bodyLoopCallsTheory.checked_function_loop_calls_ok >>
           drule_all_then ACCEPT_TAC linkedBodyLoopCallsTheory.checked_subst_consts_loop_calls_ok_mods) >>
        `!e. MEM e (DROP k ds) ==> !es'. expr_sim_inv_mods mods ce0 cx env es' ==>
             expr_body_pre_mods mods ce0 cx env e es'` by
          (rpt strip_tac >> `MEM e ds` by drule_then ACCEPT_TAC rich_listTheory.MEM_DROP_IMP >>
           `well_typed_expr env e` by drule_all_then ACCEPT_TAC frame_well_typed_exprs_member >>
           `byte_widths_expr e` by
             (irule externalBodyWidthsTheory.well_typed_expr_byte_widths >> qexists `env` >>
              qpat_assum `well_typed_expr env e` (fn typed => simp[NoAsms, typed]) >>
              rpt conj_tac >> simp[NoAsms, Abbr `env`, artifact_env_def] >>
              first_assum ACCEPT_TAC) >>
           `runtime_constant_expr mods e` by
             (qpat_assum `EVERY (runtime_constant_expr mods) ds` (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
           `alloc_limits_expr ce0 e` by drule_all_then ACCEPT_TAC exprSimSourceTheory.alloc_limits_exprs_mem >>
           qpat_assum `!e. MEM e (DROP k ds) ==> ~supported_expr_exists _ e /\ _`
             (drule_then strip_assume_tac) >>
           irule groupedDefaultPreTheory.runtime_constant_expr_body_pre_mods >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `MAP (\(n,_,ty,e). (n,ty,e)) vars = specs` by
          drule_then ACCEPT_TAC groupedKeywordDecodeTheory.compile_create_kwarg_allocas_preserves_specs >>
        `!n dst ty e. MEM (n,dst,ty,e) vars ==> MEM (n,ty) args /\ expr_type e = ty` by
          (rpt gen_tac >> strip_tac >>
           `MEM (n,ty,e) (MAP (\(n,_,ty,e). (n,ty,e)) vars)` by
             (simp[NoAsms, MEM_MAP] >> qexists `(n,dst,ty,e)` >> simp[NoAsms] >>
              first_assum ACCEPT_TAC) >>
           pop_assum mp_tac >>
           qpat_assum `MAP _ vars = specs` (fn mv =>
             qpat_assum `specs = MAP _ _` (fn sp => PURE_REWRITE_TAC [mv,sp])) >>
           `LENGTH (DROP npos args) = LENGTH ds` by
             (qpat_assum `LENGTH ds <= LENGTH args` mp_tac >>
              qpat_assum `npos = LENGTH args - LENGTH ds` (fn eq => simp[NoAsms, eq, LENGTH_DROP])) >>
           qpat_assum `npos = LENGTH args - LENGTH ds` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
           qpat_assum `LENGTH (DROP npos args) = LENGTH ds` (fn eq =>
             simp[NoAsms, MEM_MAP, EXISTS_PROD, MEM_ZIP, eq]) >>
           disch_then (qx_choose_then `j` strip_assume_tac) >>
           `j < LENGTH (DROP npos args)` by
             (qpat_assum `LENGTH (DROP npos args) = LENGTH ds` (fn eq => simp[NoAsms, eq]) >>
              first_assum ACCEPT_TAC) >>
           conj_tac
           >- (irule rich_listTheory.MEM_DROP_IMP >> qexists `npos` >>
               pure_rewrite_tac [MEM_EL] >> qexists `j` >> conj_tac >> first_assum ACCEPT_TAC) >>
           qpat_assum `MAP expr_type ds = MAP SND (DROP npos args)`
             (mp_tac o Q.AP_TERM `EL j`) >>
           qpat_assum `j < LENGTH ds` (fn jd =>
             qpat_assum `j < LENGTH (DROP npos args)` (fn ja => simp[NoAsms, EL_MAP, jd, ja])) >>
           qpat_assum `(n,ty) = EL j _` (fn arg =>
             qpat_assum `e = EL j ds` (fn expr => simp[NoAsms, GSYM arg, GSYM expr]))) >>
        `!n ty. MEM (n,ty) args ==> type_memory_bytes common.ec_env ty < 2 ** 64` by
          (qabbrev_tac `alloc_env = build_compile_env_unit mods src Internal mut name args ret code F` >>
           `common.ec_env.ce_struct_fields = alloc_env.ce_struct_fields` by
             (qpat_assum `common.ec_env.ce_struct_fields = make_struct_fields_map_mods mods` (fn sf_eq =>
               simp[NoAsms, sf_eq, Abbr `alloc_env`, build_compile_env_unit_def, ELIM_UNCURRY])) >>
           `type_memory_bytes common.ec_env = type_memory_bytes alloc_env` by
             (irule type_memory_bytes_frame >> first_assum ACCEPT_TAC) >>
           `EVERY (\(_,ty). type_memory_bytes alloc_env ty < 2 ** 64) args` by
             (qpat_assum `fn_allocs_ok_unit _ _` mp_tac >>
              simp[NoAsms, fn_allocs_ok_unit_def, Abbr `alloc_env`]) >>
           pop_assum mp_tac >>
           qpat_assum `type_memory_bytes common.ec_env = type_memory_bytes alloc_env` (fn eq =>
             simp[NoAsms, GSYM eq, EVERY_MEM, FORALL_PROD])) >>
        `no_sha256_exprs (MAP (\(_,_,_,e). e) (DROP k vars))` by
          (qpat_assum `MAP _ (DROP k vars) = DROP k ds` SUBST1_TAC >>
           qpat_assum `no_sha256_exprs ds` mp_tac >>
           simp[NoAsms, constSubstTheory.no_sha256_collections, rich_listTheory.EVERY_DROP]) >>
        `LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
           dst = Var p /\ runtime_constant_expr mods e /\ expr_type e = ty /\
           (!es'. expr_sim_inv_mods mods ce0 cx env es' ==> expr_body_pre_mods mods ce0 cx env e es') /\
           lower_value compile_expr ce0 ty e = lower_value compile_expr common.ec_env ty e /\
           lower_value compile_expr (gas_shadow_env T ce0) ty (gas_shadow_expr e) =
             lower_value compile_expr (gas_shadow_env T common.ec_env) ty (gas_shadow_expr e) /\
           evaluate_type (get_tenv cx) ty = SOME tv /\
           type_memory_bytes common.ec_env ty = type_memory_size tv /\
           type_memory_size tv + 64 < dimword (:256)) (DROP k vars) (DROP k slots)` by
          (qpat_assum `LIST_REL _ (DROP k vars) (DROP k slots)` mp_tac >>
           PURE_REWRITE_TAC [LIST_REL_EL_EQN] >> strip_tac >>
           conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `j` >> strip_tac >>
           Cases_on `EL j (DROP k vars)` >> PairCases_on `r` >>
           Cases_on `EL j (DROP k slots)` >> PairCases_on `r` >>
           rename1 `EL j (DROP k vars) = (nm,dst,ty,e)` >>
           rename1 `EL j (DROP k slots) = (row_aid,row_p,row_base,tval:type_value)` >>
           `MEM (nm,dst,ty,e) (DROP k vars)` by
             (pure_rewrite_tac [MEM_EL] >> qexists `j` >>
              conj_tac >- first_assum ACCEPT_TAC >> sym_tac >> first_assum ACCEPT_TAC) >>
           `MEM (nm,dst,ty,e) vars` by drule_then ACCEPT_TAC rich_listTheory.MEM_DROP_IMP >>
           `MEM (nm,ty) args /\ expr_type e = ty` by
             (qpat_assum `!n dst ty e. MEM (n,dst,ty,e) vars ==> _` (drule_then ACCEPT_TAC)) >>
           `MEM e (DROP k ds)` by
             (qpat_assum `MAP _ (DROP k vars) = DROP k ds` (SUBST1_TAC o SYM) >>
              simp[NoAsms, MEM_MAP] >> qexists `(nm,dst,ty,e)` >>
              simp[NoAsms] >> first_assum ACCEPT_TAC) >>
           `MEM e ds` by drule_then ACCEPT_TAC rich_listTheory.MEM_DROP_IMP >>
           `well_typed_expr env e` by drule_all_then ACCEPT_TAC frame_well_typed_exprs_member >>
           `runtime_constant_expr mods e` by
             (qpat_assum `EVERY (runtime_constant_expr mods) ds` (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
           qpat_assum `!i. i < LENGTH (DROP k vars) ==> _` (qspec_then `j` mp_tac) >>
           qpat_assum `j < LENGTH (DROP k vars)` (fn lt =>
             qpat_assum `EL j (DROP k vars) = _` (fn v =>
               qpat_assum `EL j (DROP k slots) = _` (fn s => simp[NoAsms, lt, v, s]))) >>
           strip_tac >> drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
           disch_then (strip_assume_tac o REWRITE_RULE [abiDecoderCoherenceTheory.abi_decoder_header_def]) >>
           `get_tenv cx = tenv` by
             (simp[NoAsms, Abbr `tenv`] >> first_assum ACCEPT_TAC) >>
           `type_memory_bytes common.ec_env ty < 2 ** 64` by
             (qpat_assum `!n ty. MEM (n,ty) args ==> _` (drule_then ACCEPT_TAC)) >>
           `type_memory_size tval + 64 < dimword (:256)` by
             (qpat_assum `type_memory_size tval = type_memory_bytes common.ec_env ty` SUBST1_TAC >>
              qpat_assum `type_memory_bytes common.ec_env ty < 2 ** 64` mp_tac >>
              simp[NoAsms, wordsTheory.dimword_def] >> decide_tac) >>
           `!ee. lower_value compile_expr (ee with ce_vars := FEMPTY) ty e =
                   lower_value compile_expr ee ty e /\
                 lower_value compile_expr (ee with ce_vars := FEMPTY) ty (gas_shadow_expr e) =
                   lower_value compile_expr ee ty (gas_shadow_expr e)` by
             (gen_tac >> irule runtimeDefaultCompileTheory.runtime_default_lower_value_vars_frame >>
              map_every assume_tac (CONJUNCTS runtimeDefaultCompileTheory.well_typed_expr_builtin_args_length) >>
              qpat_assum `!en x. well_typed_expr en x ==> ~supported_expr_exists _ x` (drule_then assume_tac) >>
              conj_tac >- first_assum ACCEPT_TAC >>
              (first_assum ACCEPT_TAC ORELSE (qexists `mods` >> first_assum ACCEPT_TAC))) >>
           qpat_assum `EL j (DROP k vars) = _` (fn v =>
             qpat_assum `EL j (DROP k slots) = _` (fn s => simp[NoAsms, v, s])) >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           FIRST
             [qpat_assum `!e. MEM e (DROP k ds) ==> !es'. expr_sim_inv_mods _ _ _ _ es' ==> _`
                (drule_then ACCEPT_TAC),
              qpat_assum `!ee. lower_value _ _ _ _ = _ /\ _`
                (qspec_then `common.ec_env` strip_assume_tac) >> simp[NoAsms, Abbr `ce0`] >>
                first_assum ACCEPT_TAC,
              qpat_assum `!ee. lower_value _ _ _ _ = _ /\ _`
                (qspec_then `gas_shadow_env T common.ec_env` mp_tac) >>
                simp[NoAsms, Abbr `ce0`, gasShadowCompileBaseTheory.gas_shadow_env_def] >>
                strip_tac >> first_assum ACCEPT_TAC,
              qpat_assum `get_tenv cx = tenv` SUBST1_TAC >> first_assum ACCEPT_TAC,
              sym_tac >> first_assum ACCEPT_TAC]) >>
        `!e. runtime_constant_expr mods e ==> int_calls_expr e = []` by
          (rpt (pop_assum kall_tac) >>
           `(!p e. p = expr_internal_call_root /\ runtime_constant_expr mods e ==>
                     ~supported_expr_exists p e) /\
            (!p t. p = expr_internal_call_root /\ F ==> ~supported_target_exists p t) /\
            (!p es. p = expr_internal_call_root /\ EVERY (runtime_constant_expr mods) es ==>
                      ~supported_exprs_exists p es) /\
            (!p opt. p = expr_internal_call_root /\ F ==> ~supported_opt_exists p opt) /\
            (!p fs. p = expr_internal_call_root /\ EVERY (runtime_constant_expr mods) (MAP SND fs) ==>
                      ~supported_fields_exists p fs)` by
             (ho_match_mp_tac supported_expr_exists_ind >>
              rw[runtime_constant_expr_def, supported_expr_exists_def, expr_internal_call_root_def] >>
              fs[EVERY_MEM] >> metis_tac[whitelistCheckerConstsTheory.constant_expr_runtime_constant]) >>
           map_every assume_tac (CONJUNCTS bodyExprPreFactsTheory.no_internal_call_int_calls) >>
           rpt strip_tac >> qpat_assum `!e. ~supported_expr_exists expr_internal_call_root e ==> _` irule >>
           qpat_assum `!p x. p = expr_internal_call_root /\ runtime_constant_expr mods x ==> _` (irule_at Any) >>
           simp[]) >>
        `EVERY (struct_args_unique o SND) mods` by
          (simp[NoAsms, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
           rename1 `MEM (owner,ts) mods` >>
           irule typedCopyProducerTheory.distinct_type_keys_struct_args_unique >>
           `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel owner) ts))` by
             drule_all_then ACCEPT_TAC contract_namespaces_ok_module_type_def_keys >>
           `!decls. FLAT (MAP (type_def_keys_toplevel (NONE:num option)) decls) =
             MAP (\(_,n). (NONE:num option,n)) (FLAT (MAP (type_def_keys_toplevel owner) decls)) /\
             EVERY (\(s,_). s = owner) (FLAT (MAP (type_def_keys_toplevel owner) decls))` by
             (rpt (pop_assum kall_tac) >> Induct >> simp[] >>
              Cases_on `h` >> simp[type_def_keys_toplevel_def]) >>
           pop_assum (qspec_then `ts` strip_assume_tac) >>
           qpat_assum `FLAT (MAP (type_def_keys_toplevel NONE) ts) = MAP _ _` SUBST1_TAC >>
           irule ALL_DISTINCT_MAP_INJ >>
           reverse conj_tac >- first_assum ACCEPT_TAC >>
           simp[NoAsms, FORALL_PROD] >>
           qpat_assum `EVERY _ (FLAT (MAP (type_def_keys_toplevel owner) ts))` mp_tac >>
           simp[NoAsms, EVERY_MEM, FORALL_PROD] >>
           rpt (pop_assum kall_tac) >> metis_tac[]) >>
        `exports_ok cx.layouts cx.txn.target mods exps` by
          (simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >> first_assum ACCEPT_TAC) >>
        `IS_SOME (check_contract F cx.layouts cx.txn.target mods)` by
          (qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
            simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, checked])) >>
        `EVERY (body_expr_full_ok_mods mods exps cx) (MAP (\(_,_,_,e). e) (DROP k vars))` by
          (qpat_assum `MAP _ (DROP k vars) = DROP k ds` SUBST1_TAC >>
           simp[NoAsms, EVERY_MEM] >> rpt strip_tac >>
           `MEM e ds` by drule_then ACCEPT_TAC rich_listTheory.MEM_DROP_IMP >>
           `runtime_constant_expr mods e` by
             (qpat_assum `EVERY (runtime_constant_expr mods) ds` (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
           `int_calls_expr e = []` by
             (qpat_assum `!e. runtime_constant_expr mods e ==> _` (drule_then ACCEPT_TAC)) >>
           qspecl_then [`mods`,`exps`] (map_every assume_tac o CONJUNCTS) bodySimFullMainTheory.body_sim_full_mutual_mods >>
           qpat_assum `!cx e. _ ==> body_expr_full_ok_mods mods exps cx e` irule >>
           qpat_assum `int_calls_expr e = []` (fn eq => simp[NoAsms, eq]) >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `contract_inv mods exps unit.cu_context ce0 cx` by
          (`contract_inv mods exps unit.cu_context ce0 cx =
             contract_inv mods exps unit.cu_context (base_env with ce_target := rpolicy.rpol_target) cx`
             suffices_by (disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
           qunabbrev_tac `ce0` >> qpat_assum `common.ec_env = _` SUBST1_TAC >>
           Cases_on `ret = NoneT` >> pop_assum (fn ret_eq =>
             simp[NoAsms, ret_eq, bodyInvSplitTheory.contract_inv_def, bodyInvSplitTheory.cenv_module_pins_mods_def,
                   bodyInvSplitTheory.immutable_section_layout_mods_def, update_cenv_nonreentrant_def, update_cenv_ret_abi_def])) >>
        `module_body_inv mods src src_tops ce0 cx` by
          (qunabbrev_tac `ce0` >> qpat_assum `common.ec_env = _` SUBST1_TAC >>
           Cases_on `ret = NoneT` >> pop_assum (fn ret_eq =>
             simp[NoAsms, ret_eq, bodyInvSplitTheory.module_body_inv_def, Abbr `base_env`, build_compile_env_unit_def,
                  update_cenv_nonreentrant_def, update_cenv_ret_abi_def, ELIM_UNCURRY]) >> first_assum ACCEPT_TAC) >>
        `ce0.ce_module = src` by
          (qpat_assum `module_body_inv mods src src_tops ce0 cx`
             (strip_assume_tac o REWRITE_RULE [bodyInvSplitTheory.module_body_inv_def]) >>
           first_assum ACCEPT_TAC) >>
        `get_module_code cx = ALOOKUP mods` by
          (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods` (fn eq =>
             simp[NoAsms, FUN_EQ_THM, vyperContextTheory.get_module_code_def, eq])) >>
        `ce0.ce_modules = mods /\ ce0.ce_struct_fields = make_struct_fields_map_mods mods /\
         ce0.ce_is_ctor = cx.in_deploy /\
         ALL_DISTINCT (MAP FST mods) /\
         ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
         (!owner ts. ALOOKUP mods owner = SOME ts ==>
            ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel owner) ts))) /\
         (!fname tys. ce0.ce_method_id fname tys = w2n (calldata_method_id
           (function_selector fname (vyper_to_abi_types (get_tenv cx) tys))))` by
          (qpat_assum `contract_inv mods exps _ ce0 cx`
             (strip_assume_tac o REWRITE_RULE [bodyInvSplitTheory.contract_inv_def, bodyInvSplitTheory.cenv_module_pins_mods_def]) >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           FIRST
             [simp[NoAsms, contract_keys_def] >> first_assum ACCEPT_TAC,
              rpt strip_tac >> qpat_assum `!s t. ALOOKUP mods s = SOME t ==> _`
                (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC,
              qpat_assum `get_tenv cx = type_env_all_modules mods` SUBST1_TAC >>
              qpat_assum `ce0.ce_method_id = _` SUBST1_TAC >> simp[NoAsms]]) >>
        `exprSimAbiDecodeEntryMetadata$abi_decode_root_metadata ce0 (get_tenv cx)` by
          (`exprSimAbiDecodeEntryMetadata$abi_decode_root_metadata ce0 (get_tenv cx) =
             exprSimAbiDecodeEntryMetadata$abi_decode_root_metadata common.ec_env tenv`
               suffices_by (disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
           qpat_assum `get_tenv cx = type_env_all_modules mods` SUBST1_TAC >>
           simp[NoAsms, exprSimAbiDecodeEntryMetadataTheory.abi_decode_root_metadata_def,
                Abbr `tenv`, Abbr `ce0`]) >>
        qpat_assum `exprSimAbiDecodeEntryMetadata$abi_decode_root_metadata ce0 (get_tenv cx)`
          (strip_assume_tac o REWRITE_RULE [exprSimAbiDecodeEntryMetadataTheory.abi_decode_root_metadata_def]) >>
        `!nm fields. FLOOKUP ce0.ce_struct_fields nm = SOME fields ==> ALL_DISTINCT (MAP FST fields)` by
          (rpt strip_tac >>
           qpat_assum `sfields_tenv_consistent ce0.ce_struct_fields (get_tenv cx)`
             (strip_assume_tac o REWRITE_RULE [sfields_tenv_consistent_def]) >>
           qpat_assum `!nm fields. FLOOKUP ce0.ce_struct_fields nm = SOME fields ==> _`
             (drule_then (qx_choosel_then [`fid`,`decl_fields`] strip_assume_tac)) >>
           PairCases_on `fid` >>
           qpat_assum `FLOOKUP (get_tenv cx) (fid0,fid1) = SOME (StructArgs decl_fields)` mp_tac >>
           qpat_assum `get_tenv cx = type_env_all_modules mods` (fn eq =>
             qpat_assum `ALL_DISTINCT (MAP FST mods)` (fn distinct =>
               simp[NoAsms, eq, vyperTypeConstantFoldTheory.FLOOKUP_type_env_all_modules, distinct, AllCaseEqs()])) >>
           disch_then (qx_choose_then `decls` strip_assume_tac) >>
           drule structFieldsPropsTheory.type_env_for_module_struct_mem >> strip_tac >>
           qpat_assum `MAP FST fields = MAP FST decl_fields` SUBST1_TAC >>
           `MEM (fid0,decls) mods` by (irule ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
           drule_all_then ACCEPT_TAC check_contract_struct_fields_distinct) >>
        `!owner id ts tr typ id_str.
          get_module_code cx owner = SOME ts /\ find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) ==>
          ce0.ce_hashmap_info (owner,id) = NONE /\ ce0.ce_module_var_type (owner,id) = SOME typ` by
          (qpat_assum `get_module_code cx = ALOOKUP mods` SUBST1_TAC >>
           rpt strip_tac >> drule_all linkedStorageMetadataPropsTheory.body_inv_storage_var_types_mods >>
           strip_tac >> first_assum ACCEPT_TAC) >>
        `ce0.ce_hashmap_info = build_hashmap_info_mods mods /\
         ce0.ce_module_vars = add_immutable_locations_unit
           (get_struct_fields (make_struct_fields_map_mods mods)) mods
           (add_module_var_locations_mods mods FEMPTY)` by
          (qpat_assum `contract_inv mods exps _ ce0 cx`
             (strip_assume_tac o REWRITE_RULE [bodyInvSplitTheory.contract_inv_def, bodyInvSplitTheory.cenv_module_pins_mods_def]) >>
           conj_tac >> first_assum ACCEPT_TAC) >>
        `!src1 id ts. get_module_code cx src1 = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
           ce0.ce_hashmap_info (src1,id) = NONE /\
           FLOOKUP (add_module_var_locations_mods mods FEMPTY) (src1,id) = NONE` by
          (rpt gen_tac >> strip_tac >>
           `ALOOKUP mods src1 = SOME ts` by
             (qpat_assum `get_module_code cx = ALOOKUP mods` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
           `!decls own fm ht.
             (own <> src1 \/ find_var_decl_by_name id decls = NONE) ==>
             build_hashmap_info_src own decls ht (src1,id) = ht (src1,id) /\
             FLOOKUP (add_module_var_locations_src own decls fm) (src1,id) = FLOOKUP fm (src1,id)` by
             (rpt (pop_assum kall_tac) >> Induct >>
              simp[build_hashmap_info_src_def, add_module_var_locations_src_def] >>
              Cases_on `h` >>
              simp[build_hashmap_info_src_def, add_module_var_locations_src_def, vyperStateTheory.find_var_decl_by_name_def] >>
              rpt gen_tac >> strip_tac >> BasicProvers.every_case_tac >>
              gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
           `!ms fm. ALL_DISTINCT (MAP FST ms) /\
             (case ALOOKUP ms src1 of NONE => T | SOME ts => find_var_decl_by_name id ts = NONE) ==>
             build_hashmap_info_mods ms (src1,id) = NONE /\
             FLOOKUP (add_module_var_locations_mods ms fm) (src1,id) = FLOOKUP fm (src1,id)` by
             (qpat_assum `!decls own fm ht. _` mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
              Induct >> simp[build_hashmap_info_src_def, build_hashmap_info_mods_def, add_module_var_locations_mods_def] >>
              gen_tac >> PairCases_on `h` >>
              simp[build_hashmap_info_mods_def, add_module_var_locations_mods_def] >>
              rpt gen_tac >> Cases_on `src1 = h0` >> gvs[] >> strip_tac
              >- (`ALOOKUP ms h0 = NONE` by simp[ALOOKUP_NONE] >> gvs[] >> metis_tac[]) >>
              metis_tac[]) >>
           pop_assum (qspecl_then [`mods`,`FEMPTY`] mp_tac) >>
           qpat_assum `ALOOKUP mods src1 = SOME ts` (fn at_mod =>
             qpat_assum `find_var_decl_by_name id ts = NONE` (fn no_var =>
               qpat_assum `ALL_DISTINCT (MAP FST mods)` (fn distinct =>
                 qpat_assum `ce0.ce_hashmap_info = build_hashmap_info_mods mods` (fn eq =>
                   simp[NoAsms, at_mod, no_var, distinct, eq]))))) >>
        `!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==> ce0.ce_hashmap_info nsid = NONE` by
          (PairCases >> rpt strip_tac >>
           drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
           qpat_assum `!src1 id ts. get_module_code cx src1 = SOME ts /\ _ ==> ce0.ce_hashmap_info _ = NONE /\ _`
             drule_all >> strip_tac >> first_assum ACCEPT_TAC) >>
        `place_map_tables_agree_on_defined ce0 env` by
          (pure_rewrite_tac [placeTypingPropsTheory.place_map_tables_agree_on_defined_def] >>
           PairCases >> rpt strip_tac >>
           qpat_assum `env_consistent env cx es`
             (strip_assume_tac o REWRITE_RULE [env_consistent_def, env_context_consistent_def]) >>
           Cases_on `vt` >> simp[NoAsms]
           >- (Cases_on `FLOOKUP env.bare_globals (nsid0,nsid1)`
               >- (qpat_assum `!ss id ty. FLOOKUP env.toplevel_vtypes (ss,id) = SOME (Type ty) /\ _ ==> _`
                     (drule_all_then strip_assume_tac) >>
                   qpat_assum `!owner id ts tr typ id_str. _ ==> ce0.ce_hashmap_info _ = NONE /\ _`
                     drule_all >> simp[NoAsms] >> strip_tac >> first_assum ACCEPT_TAC) >>
               qpat_assum `!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==> ce0.ce_hashmap_info nsid = NONE`
                 drule >> simp[NoAsms]) >>
           qpat_assum `!ss id kt vt. FLOOKUP env.toplevel_vtypes (ss,id) = SOME (HashMapT kt vt) ==> _`
             (drule_then strip_assume_tac) >>
           drule_all linked_entry_hashmap_info >> simp[NoAsms]) >>
        `!owner id loc. FLOOKUP env.bare_globals (owner,id) <> NONE /\
           FLOOKUP ce0.ce_module_vars (owner,id) = SOME loc ==> ?off. loc = ImmutableLoc off` by
          (rpt gen_tac >> strip_tac >>
           `?typ. FLOOKUP env.bare_globals (owner,id) = SOME typ` by
             (qpat_assum `FLOOKUP env.bare_globals (owner,id) <> NONE` mp_tac >>
              Cases_on `FLOOKUP env.bare_globals (owner,id)` >> simp[NoAsms]) >>
           drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
           qpat_assum `!src1 id ts. get_module_code cx src1 = SOME ts /\ _ ==> _`
             (drule_all_then strip_assume_tac) >>
           `!ts fm tag. FLOOKUP (add_annotated_immutables_src tag ts fm) (owner,id) = SOME loc ==>
              FLOOKUP fm (owner,id) = SOME loc \/ ?off. loc = ImmutableLoc off` by
             (rpt (pop_assum kall_tac) >> Induct >> simp[add_annotated_immutables_src_def] >>
              Cases_on `h` >> simp[add_annotated_immutables_src_def] >> rpt gen_tac >>
              BasicProvers.every_case_tac >> simp[] >> strip_tac >> first_x_assum drule >>
              simp[finite_mapTheory.FLOOKUP_UPDATE] >> IF_CASES_TAC >> simp[] >> metis_tac[]) >>
           `!ms fm. FLOOKUP (add_annotated_immutables_mods ms fm) (owner,id) = SOME loc ==>
              FLOOKUP fm (owner,id) = SOME loc \/ ?off. loc = ImmutableLoc off` by
             (qpat_assum `!ts fm tag. _` mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
              Induct >> simp[add_annotated_immutables_mods_def] >>
              gen_tac >> PairCases_on `h` >>
              simp[add_annotated_immutables_mods_def] >> rpt strip_tac >> metis_tac[]) >>
           `!ms sf fm. FLOOKUP (add_immutable_locations_unit sf ms fm) (owner,id) = SOME loc ==>
              FLOOKUP fm (owner,id) = SOME loc \/ ?off. loc = ImmutableLoc off` by
             (qpat_assum `!ms fm. _` mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
              Cases >> simp[add_immutable_locations_unit_def, add_annotated_immutables_mods_def] >>
              gen_tac >> PairCases_on `h` >> Cases_on `t` >> Cases_on `h0` >>
              simp[add_immutable_locations_unit_def] >>
              metis_tac[compileVyperTheory.add_immutable_locations_FLOOKUP, add_annotated_immutables_mods_def]) >>
           qpat_assum `FLOOKUP ce0.ce_module_vars (owner,id) = SOME loc` mp_tac >>
           qpat_assum `ce0.ce_module_vars = _` SUBST1_TAC >>
           disch_tac >> qpat_assum `!ms sf fm. _` drule >>
           qpat_assum `FLOOKUP (add_module_var_locations_mods mods FEMPTY) (owner,id) = NONE`
             (fn eq => simp[NoAsms, eq])) >>
        `bare_globals_complete env.bare_globals cx` by
          (qpat_assum `env_consistent env cx es`
             (strip_assume_tac o REWRITE_RULE [env_consistent_def, env_context_consistent_def]) >>
           first_assum ACCEPT_TAC) >>
        `!owner id off. FLOOKUP ce0.ce_module_vars (owner,id) = SOME (ImmutableLoc off) ==>
           ?typ size. FLOOKUP env.bare_globals (owner,id) = SOME typ /\
             immutable_region_mods mods owner id off size /\
             off + size <= imm_len_mods mods /\
             (!tv. evaluate_type (get_tenv cx) typ = SOME tv ==> size = type_memory_size tv)` by
          (map_every qx_gen_tac [`iowner`,`iid`,`ioff`] >> disch_tac >>
           qpat_assum `immutable_section_layout_mods mods ce0`
             (strip_assume_tac o REWRITE_RULE [bodyInvSplitTheory.immutable_section_layout_mods_def]) >>
           `?ibytes. immutable_region_mods mods iowner iid ioff ibytes` by
             (qpat_assum `!src nm off. FLOOKUP ce0.ce_module_vars (src,nm) = _ <=> _`
               (qspecl_then [`iowner`,`iid`,`ioff`] mp_tac) >>
              qpat_assum `FLOOKUP ce0.ce_module_vars (iowner,iid) = SOME (ImmutableLoc ioff)`
                (fn loc => simp[NoAsms, loc])) >>
           `ioff + ibytes <= imm_len_mods mods` by
             (qpat_assum `!src nm off size. immutable_region_mods mods src nm off size ==> _`
               (drule_then ACCEPT_TAC)) >>
           qpat_assum `immutable_region_mods mods iowner iid ioff ibytes`
             (qx_choosel_then [`tdecls`,`imm_pre`,`imm_post`,`vis0`,`typ`,`slot0`] strip_assume_tac o
              REWRITE_RULE [bodyInvSplitTheory.immutable_region_mods_def]) >>
           `get_module_code cx iowner = SOME tdecls` by
             (qpat_assum `get_module_code cx = ALOOKUP mods` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
           `MEM (VariableDecl vis0 Immutable iid typ slot0) tdecls` by
             (qpat_assum `tdecls = _` SUBST1_TAC >> simp[NoAsms, MEM_APPEND]) >>
           `FLOOKUP env.bare_globals (iowner,iid) = SOME typ` by
             (qpat_assum `bare_globals_complete env.bare_globals cx`
               (irule o REWRITE_RULE [bare_globals_complete_def]) >>
              qexistsl [`slot0`,`Immutable`,`tdecls`,`vis0`] >>
              simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC) >>
           qexistsl [`typ`,`ibytes`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           qx_gen_tac `ivt` >> disch_tac >>
           `type_memory_bytes ce0 typ = type_memory_size ivt` by
             (irule linkedStructMemorySizeTheory.make_struct_fields_map_mods_memory_size >>
              qexistsl [`F`,`get_tenv cx`,`mods`] >> rpt conj_tac >>
              TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
              qpat_assum `get_tenv cx = type_env_all_modules mods` SUBST1_TAC >> simp[NoAsms]) >>
           qpat_assum `ibytes = _` SUBST1_TAC >>
           qpat_assum `ce0.ce_struct_fields = make_struct_fields_map_mods mods` (SUBST1_TAC o SYM) >>
           simp[NoAsms, structFieldsPropsTheory.type_mem_bytes_type_memory_bytes] >>
           first_assum ACCEPT_TAC) >>
        `!owner id ox typ ivt. FLOOKUP ce0.ce_module_vars (owner,id) = SOME (ImmutableLoc ox) /\
           FLOOKUP env.bare_globals (owner,id) = SOME typ /\ evaluate_type (get_tenv cx) typ = SOME ivt ==>
           immutable_region_mods mods owner id ox (type_memory_size ivt) /\
           ox + type_memory_size ivt <= imm_len_mods mods` by
          (rpt gen_tac >> strip_tac >>
           qpat_assum `!owner id off. FLOOKUP ce0.ce_module_vars (owner,id) = SOME (ImmutableLoc off) ==> _`
             (drule_then (qx_choosel_then [`ity`,`ibytes`] strip_assume_tac)) >>
           `ity = typ` by
             (qpat_assum `FLOOKUP env.bare_globals _ = SOME ity` mp_tac >>
              qpat_assum `FLOOKUP env.bare_globals _ = SOME typ` (fn eq => simp[NoAsms, eq])) >>
           `ibytes = type_memory_size ivt` by
             (qpat_assum `!tv. evaluate_type (get_tenv cx) ity = SOME tv ==> _`
                (qspec_then `ivt` mp_tac) >>
              qpat_assum `ity = typ` (fn eq =>
                qpat_assum `evaluate_type (get_tenv cx) typ = SOME ivt` (fn et => simp[NoAsms, eq, et]))) >>
           qpat_assum `ibytes = type_memory_size ivt` (SUBST1_TAC o SYM) >>
           conj_tac >> first_assum ACCEPT_TAC) >>
        `bare_globals_layout ce0.ce_is_ctor ce0.ce_module_var_type ce0.ce_module_vars
           ce0.ce_modules cx env.bare_globals env.bare_global_assignable` by
          (pure_rewrite_tac [bare_globals_layout_def] >>
           rpt conj_tac >> TRY (rpt strip_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
           FIRST
             [rpt strip_tac >>
              qpat_assum `!owner id off. FLOOKUP ce0.ce_module_vars (owner,id) = SOME (ImmutableLoc off) ==> _`
                (drule_then (qx_choosel_then [`ity`,`ibytes`] strip_assume_tac)) >>
              qexists `ity` >> first_assum ACCEPT_TAC,
              rpt strip_tac >> drule_all_then ACCEPT_TAC bodySimEntryTheory.body_inv_bare_global_type_mods,
              qpat_assum `ce0.ce_modules = mods` SUBST1_TAC >>
              qpat_assum `get_module_code cx = ALOOKUP mods` SUBST1_TAC >> simp[NoAsms] >> NO_TAC,
              qpat_assum `ce0.ce_modules = mods` SUBST1_TAC >> first_assum ACCEPT_TAC,
              qpat_assum `get_module_code cx = ALOOKUP mods` SUBST1_TAC >> first_assum ACCEPT_TAC,
              map_every qx_gen_tac [`sown`,`i1`,`i2`,`tya`,`tyb`,`xa`,`xb`,`vta`,`vtb`] >> strip_tac >>
              `immutable_region_mods mods sown i1 xa (type_memory_size vta)` by
                (qpat_assum `!ow i x typ vt. FLOOKUP ce0.ce_module_vars (ow,i) = SOME (ImmutableLoc x) /\ _ /\ _ ==> _`
                   (qspecl_then [`sown`,`i1`,`xa`,`tya`,`vta`] mp_tac) >>
                 (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
                 strip_tac >> first_assum ACCEPT_TAC) >>
              `immutable_region_mods mods sown i2 xb (type_memory_size vtb)` by
                (qpat_assum `!ow i x typ vt. FLOOKUP ce0.ce_module_vars (ow,i) = SOME (ImmutableLoc x) /\ _ /\ _ ==> _`
                   (qspecl_then [`sown`,`i2`,`xb`,`tyb`,`vtb`] mp_tac) >>
                 (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
                 strip_tac >> first_assum ACCEPT_TAC) >>
              qpat_assum `immutable_section_layout_mods mods ce0`
                (strip_assume_tac o REWRITE_RULE [bodyInvSplitTheory.immutable_section_layout_mods_def]) >>
              qpat_assum `!s1 n1 o1 l1 s2 n2 o2 l2. _ ==> regions_disjoint o1 l1 o2 l2` mp_tac >>
              qpat_assum `immutable_region_mods mods _ i1 _ _` mp_tac >>
              qpat_assum `immutable_region_mods mods _ i2 _ _` mp_tac >>
              qpat_assum `i1 <> i2` mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[pairTheory.PAIR_EQ]]) >>
        `imm_len_mods mods < dimword (:256)` by
          (qpat_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
           qpat_assum `classify_functions_unit _ _ = _` (fn cls =>
             simp[NoAsms, lower_vyper_runtime_unit_mods_def, cls, AllCaseEqs(),
               GSYM bodyInvSplitTheory.imm_len_mods_def]) >>
           strip_tac >> qpat_assum `imm_len_mods mods < 0x6000` mp_tac >>
           simp[NoAsms, wordsTheory.dimword_def] >> decide_tac) >>
        `env.current_src = ce0.ce_module` by
          (qpat_assum `ce0.ce_module = src` SUBST1_TAC >> simp[NoAsms, Abbr `env`, artifact_env_def]) >>
        `!owner id typ. FLOOKUP env.bare_globals (owner,id) = SOME typ /\
          (~cx_const_name_mods mods (owner,id) \/ IS_SOME (FLOOKUP env.bare_global_assignable (owner,id))) ==>
          (owner = env.current_src ==> owner = ce0.ce_module) /\
          (IS_SOME (FLOOKUP ce0.ce_module_vars (owner,id)) ==> ?ox.
             FLOOKUP ce0.ce_module_vars (owner,id) = SOME (ImmutableLoc ox) /\
             !ivt. evaluate_type (get_tenv cx) typ = SOME ivt ==> ox + type_memory_size ivt < dimword (:256))` by
          (map_every qx_gen_tac [`owner`,`id`,`typ`] >>
           disch_then (assume_tac o CONJUNCT1) >> conj_tac
           >- (qpat_assum `env.current_src = ce0.ce_module` (fn eq => simp[NoAsms, eq])) >>
           pure_rewrite_tac [IS_SOME_EXISTS] >>
           disch_then (qx_choose_then `iloc` assume_tac) >>
           `FLOOKUP env.bare_globals (owner,id) <> NONE` by
             (qpat_assum `FLOOKUP env.bare_globals (owner,id) = SOME typ` (fn eq => simp[NoAsms, eq])) >>
           qpat_assum `!owner id loc. FLOOKUP env.bare_globals (owner,id) <> NONE /\ _ ==> _`
             (drule_all_then (qx_choose_then `ioff` assume_tac)) >>
           qpat_assum `iloc = ImmutableLoc ioff` SUBST_ALL_TAC >>
           qexists `ioff` >> conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `ivt` >> disch_tac >>
           qpat_assum `!ow i x typ vt. FLOOKUP ce0.ce_module_vars (ow,i) = SOME (ImmutableLoc x) /\ _ /\ _ ==> _`
             (drule_all_then strip_assume_tac) >>
           qpat_assum `imm_len_mods mods < dimword (:256)` mp_tac >>
           qpat_assum `ioff + type_memory_size ivt <= imm_len_mods mods` mp_tac >> decide_tac) >>
        `expr_sim_inv_mods mods ce0 cx env es` by
          (pure_rewrite_tac [expr_sim_inv_mods_def] >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           FIRST
             [simp[NoAsms, Abbr `env`, artifact_env_def] >> NO_TAC,
              qpat_assum `es.outcomes = SOME []`
                (fn eq => simp[NoAsms, eq, outcomes_accounts_typed_def] >> NO_TAC),
              qpat_assum `es.scopes = [FEMPTY]`
                (fn eq => simp[NoAsms, eq, popped_keys_indexed_def] >> NO_TAC),
              rpt gen_tac >> strip_tac >> conj_tac >> first_assum (drule_then ACCEPT_TAC)]) >>
        `gas_origin_ptr_path (ARB,0,EMPTY,unit.cu_context,fn,[])
           (start,FEMPTY,entry_taint) [] (OK u,Gu,tu)` by
          (qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK u,Gu,tu)` MATCH_ACCEPT_TAC) >>
        `selected_registration_frame (vs with vs_outcomes := []) entry_taint seed tu` by
          (qpat_assum `selected_registration_frame start entry_taint a ta` mp_tac >>
           qpat_assum `selected_registration_frame a ta u tu` mp_tac >>
           simp[NoAsms, selected_registration_frame_def, Abbr `seed`, Abbr `start`] >>
           rpt strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           first_assum (fn th => first_assum (fn th' => ACCEPT_TAC (TRANS th th')))) >>
        qpat_assum `selected_registration_frame (vs with vs_outcomes := []) entry_taint seed tu`
          (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def, venom_state_accfupds, entry_taint_def]) >>
        qpat_assum `initial_venom_state_rel_mods mods am tx vs`
          (strip_assume_tac o REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
        `seed.vs_initial_fmp = vs.vs_initial_fmp` by
          (drule_all_then (mp_tac o CONJUNCT1) decoderOriginAllocationFrameTheory.decoder_origin_path_allocation_frame >>
           simp[NoAsms, Abbr `seed`, Abbr `start`]) >>
        `alloca_history fn start` by
          (irule allocaHistoryTheory.alloca_history_empty >> conj_tac >> first_assum ACCEPT_TAC) >>
        `alloca_history fn u` by
          drule_all_then ACCEPT_TAC bodyFullPathHistoryTheory.body_full_path_alloca_history >>
        `alloca_history fn seed` by
          (irule allocaHistoryTheory.alloca_history_frame >> qexists `u` >>
           simp[NoAsms, Abbr `seed`] >> first_assum ACCEPT_TAC) >>
        qpat_assum `selected_registration_resources unit.cu_context fn ARB 0 residual u`
          (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
        `alloca_inv seed /\ alloca_frontier_inv unit.cu_context fn ARB seed` by
          (`(alloca_inv seed <=> alloca_inv u) /\
            (alloca_frontier_inv unit.cu_context fn ARB seed <=> alloca_frontier_inv unit.cu_context fn ARB u)` by
              (irule calldataDynOwnedTheory.calldata_alloca_invariants_fields >> simp[NoAsms, Abbr `seed`]) >>
           conj_tac >> ASM_REWRITE_TAC []) >>
        `alloca_room unit.cu_context fn seed` by
          drule_all_then ACCEPT_TAC registration_frontier_alloca_room >>
        `seed.vs_fmp = seed.vs_initial_fmp` by
          (qpat_assum `seed.vs_fmp = vs.vs_fmp` SUBST1_TAC >> ASM_REWRITE_TAC []) >>
        `(ctx_has_dalloca unit.cu_context ==> unit_alloca_budget unit.cu_context <= w2n seed.vs_initial_fmp /\
           w2n seed.vs_initial_fmp < 2 ** 254)` by ASM_REWRITE_TAC [] >>
        `fmp_room unit.cu_context fn seed` by
          drule_all_then ACCEPT_TAC entryReachBodyFmpTheory.entry_frontier_fmp_room >>
        `allocas_from 0 seed /\ (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp seed) /\
         ~seed.vs_halted /\ seed.vs_current_bb = residual.cs_current_bb /\
         seed.vs_inst_idx = LENGTH residual.cs_current_insts` by
          (rpt conj_tac >> FIRST
             [simp[NoAsms, Abbr `seed`] >> first_assum ACCEPT_TAC,
              simp[NoAsms, Abbr `seed`, allocas_from_def] >> NO_TAC,
              `allocas_below_fmp seed <=> allocas_below_fmp u` by
                simp[NoAsms, Abbr `seed`, allocas_below_fmp_def] >>
              disch_tac >> qpat_assum `(allocas_below_fmp seed <=> _)` SUBST1_TAC >>
              qpat_assum `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp u /\ _`
                (drule_then (ACCEPT_TAC o CONJUNCT1))]) >>
        `cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
         cx.txn.code = tx.code /\ ~cx.in_deploy` by
          simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
        `~ce0.ce_is_ctor` by
          (qpat_assum `ce0.ce_is_ctor <=> cx.in_deploy` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        `base_env.ce_return_pc = NONE /\ base_env.ce_return_buf = NONE /\ base_env.ce_imm_alloca = NONE` by
          simp[NoAsms, Abbr `base_env`, build_compile_env_unit_def, UNCURRY, LET_THM] >>
        `ce0.ce_vars = FEMPTY /\ common.ec_env.ce_return_pc = NONE /\
           common.ec_env.ce_return_buf = NONE /\ common.ec_env.ce_imm_alloca = NONE` by
          (simp[NoAsms, Abbr `ce0`] >>
           qpat_assum `common.ec_env = _` SUBST1_TAC >>
           Cases_on `ret = NoneT` >> pop_assum (fn rt =>
             simp[NoAsms, rt, update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `ce0.ce_return_pc = NONE` by
          (simp[NoAsms, Abbr `ce0`] >> first_assum ACCEPT_TAC) >>
        `storage_vars_rel ce0 cx /\ transient_vars_rel ce0 cx` by
          (irule entryModuleLocationsTheory.unit_module_locations_slot_relations >>
           qexistsl_tac [`am`,`exps`,`mods`,`tx`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `immutables_section_rel_mods mods
           (case ALOOKUP es.immutables cx.txn.target of
              NONE => empty_immutables | SOME imms => imms) seed.vs_data_section` by
          (qpat_assum `cx.txn.target = tx.target` SUBST1_TAC >>
           qpat_assum `es.immutables = am.immutables` SUBST1_TAC >>
           qpat_assum `seed.vs_data_section = vs.vs_data_section` SUBST1_TAC >>
           pure_rewrite_tac [GSYM e2eDefsTheory.account_immutables_def] >> first_assum ACCEPT_TAC) >>
        `!owner. immutables_rel ce0 cx.txn.target owner F es seed` by
          (qx_gen_tac `owner` >> Cases_on `ALOOKUP es.immutables cx.txn.target`
           >- simp[immutables_rel_def] >>
           qpat_assum `immutables_section_rel_mods mods _ seed.vs_data_section` mp_tac >>
           qpat_assum `immutable_section_layout_mods mods ce0` mp_tac >>
           simp[NoAsms, immutables_rel_def, bodyInvSplitTheory.immutable_section_layout_mods_def,
             immutables_section_rel_mods_def] >>
           ntac 2 strip_tac >>
           map_every qx_gen_tac [`imm_id`,`imm_ty`,`imm_val`,`byte_off`] >> strip_tac >>
           qpat_assum `!src nm off sz. immutable_region_mods mods src nm off sz ==> ?ity value. _`
             (drule_then (qx_choosel_then [`ity`,`ivalue`] strip_assume_tac)) >>
           `imm_ty = ity /\ imm_val = ivalue` by
             (qpat_assum `FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => _ | SOME _ => _) imm_id = _` mp_tac >>
              qpat_assum `ALOOKUP es.immutables cx.txn.target = SOME _` (fn eq =>
                qpat_assum `FLOOKUP (get_source_immutables owner _) imm_id = SOME (ity,ivalue)` (fn kv =>
                  simp[NoAsms, eq, kv, pairTheory.PAIR_EQ]))) >>
           qpat_assum `imm_ty = ity` SUBST_ALL_TAC >> qpat_assum `imm_val = ivalue` SUBST_ALL_TAC >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           qpat_assum `type_memory_size ity = _` SUBST1_TAC >>
           qpat_assum `!src nm off sz. immutable_region_mods mods src nm off sz ==> off + sz <= _`
             irule >> qexistsl_tac [`imm_id`,`owner`] >> first_assum ACCEPT_TAC) >>
        `immutable_frame_mods fn ce0 cx es seed` by
          (qpat_assum `~ce0.ce_is_ctor` (fn nc =>
             simp[NoAsms, bodyFullPostsModsTheory.immutable_frame_mods_def,
               bodyInvSplitTheory.immutables_rel_mods_def, bodyInvSplitTheory.immutable_alloca_sep_mods_def,
               exprLoweringPropsTheory.immutable_alloca_sep_def, exprLoweringPropsTheory.immutable_decl_sep_def, nc]) >>
           rpt strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
        `es.accounts = seed.vs_accounts /\ es.tStorage = seed.vs_transient /\
           es.logs = [] /\ seed.vs_logs = [] /\ es.pending_deletions = seed.vs_pending_deletions /\
           seed.vs_requests = [] /\ seed.vs_outcomes = []` by
          (drule_then mp_tac entryStateRelTheory.send_call_value_accounts >>
           disch_then SUBST1_TAC >>
           simp[NoAsms, Abbr `es_in`, initial_state_def] >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           map_every (fn p => qpat_assum p SUBST1_TAC)
             [`seed.vs_accounts = vs.vs_accounts`,`seed.vs_transient = vs.vs_transient`,
              `seed.vs_logs = vs.vs_logs`,`seed.vs_pending_deletions = vs.vs_pending_deletions`,
              `seed.vs_requests = vs.vs_requests`] >>
           TRY (first_assum ACCEPT_TAC >> NO_TAC) >> TRY (sym_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
           TRY (simp[NoAsms, Abbr `seed`] >> NO_TAC) >>
           qpat_assum `vs.vs_accounts = _` SUBST1_TAC >>
           simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, e2eDefsTheory.accounts_after_transfer_def]) >>
        `call_ctx_rel cx.txn seed.vs_call_ctx seed.vs_tx_ctx seed.vs_block_ctx /\ seed.vs_code = cx.txn.code` by
          (map_every (fn p => qpat_assum p SUBST1_TAC)
             [`seed.vs_call_ctx = vs.vs_call_ctx`,`seed.vs_tx_ctx = vs.vs_tx_ctx`,
              `seed.vs_block_ctx = vs.vs_block_ctx`,`seed.vs_code = vs.vs_code`] >>
           qpat_assum `venom_env_rel tx vs`
             (strip_assume_tac o REWRITE_RULE [venom_env_rel_def]) >>
           `call_ctx_rel cx.txn vs.vs_call_ctx vs.vs_tx_ctx vs.vs_block_ctx =
            call_ctx_rel tx vs.vs_call_ctx vs.vs_tx_ctx vs.vs_block_ctx` by
             simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, call_ctx_rel_def, tx_env_ok_def] >>
           qpat_assum `call_ctx_rel cx.txn _ _ _ = _` SUBST1_TAC >>
           conj_tac >- first_assum ACCEPT_TAC >> qpat_assum `cx.txn.code = tx.code` SUBST1_TAC >>
           first_assum ACCEPT_TAC) >>
        `seed.vs_call_ctx.cc_address = cx.txn.target` by
          (qpat_assum `call_ctx_rel cx.txn seed.vs_call_ctx seed.vs_tx_ctx seed.vs_block_ctx`
             (strip_assume_tac o REWRITE_RULE [call_ctx_rel_def]) >> first_assum ACCEPT_TAC) >>
        `!H:(bool # bytes32 # type_value) list # num list. state_rel H fn ce0 cx es seed` by
          (gen_tac >> pure_rewrite_tac [state_rel_def] >> rpt conj_tac >>
           TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           FIRST
             [qpat_assum `ce0.ce_vars = FEMPTY` (fn ev => simp[NoAsms, ev, local_ptrs_rel_def, local_region_def]) >> NO_TAC,
              qpat_assum `~ce0.ce_is_ctor` (fn nc => simp[NoAsms, nc]) >> first_assum MATCH_ACCEPT_TAC,
              map_every (fn p => qpat_assum p SUBST1_TAC)
                [`es.accounts = seed.vs_accounts`,`es.tStorage = seed.vs_transient`,
                 `es.logs = []`,`seed.vs_logs = []`,`es.outcomes = SOME []`,
                 `es.requests = []`,`seed.vs_requests = []`,`seed.vs_outcomes = []`,
                 `seed.vs_code = cx.txn.code`] >>
              simp[NoAsms, storage_rel_def, transient_rel_def, contract_storage_def,
                   contract_transient_def, logs_rel_def, accounts_rel_def,
                   accounts_agree_def, transient_agree_def] >>
              qpat_assum `seed.vs_call_ctx.cc_address = cx.txn.target` (fn addr =>
                qpat_assum `es.accounts = seed.vs_accounts` (fn acct =>
                  qpat_assum `es.tStorage = seed.vs_transient` (fn tr =>
                    qpat_assum `seed.vs_code = cx.txn.code` (fn code_eq =>
                      qpat_assum `es.logs = []` (fn s_log =>
                        qpat_assum `seed.vs_logs = []` (fn v_log =>
                          simp[NoAsms, addr, acct, tr, code_eq, s_log, v_log,
                               accountsRelPropsTheory.storage_agree_refl]))))))]) >>
        `!H:(bool # bytes32 # type_value) list # num list. stmt_state_rel H unit.cu_context fn ce0 cx es seed` by
          (qx_gen_tac `H` >>
           `ce0.ce_imm_alloca = NONE` by (simp[NoAsms, Abbr `ce0`] >> first_assum ACCEPT_TAC) >>
           qpat_assum `~ce0.ce_is_ctor` (fn nc =>
             qpat_assum `ce0.ce_imm_alloca = NONE` (fn im =>
               simp[NoAsms, exprLoweringPropsTheory.stmt_state_rel_def,
                 exprLoweringPropsTheory.immutable_alloca_sep_def,
                 exprLoweringPropsTheory.immutable_decl_sep_def,
                 immutable_base_zero_def, nc, im])) >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           FIRST [first_assum MATCH_ACCEPT_TAC,
             simp[NoAsms, Abbr `seed`] >> first_assum ACCEPT_TAC]) >>
        pop_assum $ mk_asm "seed_stmt_rel" >>
        `!H:(bool # bytes32 # type_value) list # num list. dead_lo_ok H (cx_dead H cx) 0 ce0 cx` by
          (qpat_assum `~ce0.ce_is_ctor` (fn nc => simp[NoAsms, bodyPtrDefsTheory.dead_lo_ok_def, nc])) >>
        `!H:(bool # bytes32 # type_value) list # num list. ghost_inv_at (cx_dead H cx) 0 NONE ce0 cx es Gu tu seed` by
          (qpat_assum `ce0.ce_vars = FEMPTY` (fn ev =>
             qpat_assum `ce0.ce_return_pc = NONE` (fn pc =>
               simp[NoAsms, ev, pc, bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.return_buf_ptr_def])) >>
           gen_tac >> conj_tac >-
             (pure_rewrite_tac [bodyPtrDefsTheory.stor_taint_ok_at_def] >>
              qpat_assum `tu.t_stor = _` SUBST1_TAC >>
              qpat_assum `tu.t_trans = _` SUBST1_TAC >>
              qpat_assum `tu.t_imm = _` SUBST1_TAC >> simp[NoAsms]) >>
           first_assum ACCEPT_TAC) >>
        `storage_trace_domain cx (initial_state am []) es.storage_trace` by
          (qpat_assum `es.storage_trace = []` SUBST1_TAC >> EVAL_TAC >> simp[NoAsms]) >>
        `!H. valid_horizon cx (initial_state am []) H es.storage_trace ==>
          stmt_state_rel H unit.cu_context fn ce0 cx es seed /\ immutable_frame_mods fn ce0 cx es seed /\
          storage_well_formed_on cx es (FST H) /\ ghost_inv_at (cx_dead H cx) 0 NONE ce0 cx es Gu tu seed` by
          (qx_gen_tac `H` >>
           disch_then (strip_assume_tac o REWRITE_RULE [vyperStorageFootprintTheory.valid_horizon_def]) >>
           conj_tac >- (asm "seed_stmt_rel" irule) >>
           conj_tac >- first_assum ACCEPT_TAC >>
           reverse conj_tac >-
             (qpat_assum `!hh. ghost_inv_at (cx_dead hh cx) 0 NONE ce0 cx es Gu tu seed` (qspec_then `H` ACCEPT_TAC)) >>
           `storage_well_formed_on cx es_in (FST H)` by
             (irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
              qexists `initial_state am []` >>
              simp[NoAsms, Abbr `es_in`, initial_state_def] >>
              qpat_assum `storage_well_formed_on cx (initial_state am []) (FST H)` mp_tac >>
              simp[NoAsms, initial_state_def]) >>
           drule_all_then ACCEPT_TAC vyperExternalEntryStorageFrameTheory.send_call_value_preserves_storage_well_formed_on) >>
        qpat_assum `gas_shadow_unit unit shadow_unit`
          (strip_assume_tac o REWRITE_RULE [gasShadowUnitTheory.gas_shadow_unit_def]) >>
        `MEM fn unit.cu_context.ctx_functions /\ MEM shadow_fn shadow_unit.cu_context.ctx_functions` by
          (conj_tac >> drule_then ACCEPT_TAC lookup_function_MEM) >>
        `ctx_inst_ids_distinct unit.cu_context` by
          (drule lowering_context_ok_static_integrity >> strip_tac >> first_assum ACCEPT_TAC) >>
        `!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
          (drule lowering_context_ok_bridge >> strip_tac >>
           qpat_x_assum `EVERY (\f. ALL_DISTINCT (fn_labels f) /\ _) _` mp_tac >>
           simp[EVERY_MEM] >> disch_then (qspec_then `fn` mp_tac) >>
           simp[] >> strip_tac >> rpt strip_tac >>
           `venomInst$lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
             (irule venomExecPropsTheory.MEM_lookup_block >>
              conj_tac >- (qpat_assum `ALL_DISTINCT (fn_labels fn)`
                (ACCEPT_TAC o REWRITE_RULE [fn_labels_def])) >>
              simp[NoAsms] >> first_assum ACCEPT_TAC) >>
           qpat_assum `!label bb. venomInst$lookup_block label fn.fn_blocks = SOME bb ==> _`
             (irule o SPEC_ALL) >> qexists `bb.bb_label` >> first_assum ACCEPT_TAC) >>
        (let
           fun use pat k th = qpat_assum pat (mp_then Any k th)
         in
           use `compile_init_kwargs _ (DROP k vars) _ 0 _ residual = ((),cut)`
           (use `compile_init_kwargs _ _ _ 0 _ shadow_residual = ((),shadow_cut)`
           (use `fn_has_code residual cut fn`
           (use `fn_has_code shadow_residual shadow_cut shadow_fn`
           (use `shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context`
           (use `body_const_cells_agree_mods mods cx env es`
           (use `check_contract F am.layouts tx.target mods = SOME art`
           (use `storage_trace_domain cx (initial_state am []) es.storage_trace`
           (use `EVERY (^row22_kw_alloc residual seed Gu tu) (DROP k slots)`
           (use `EVERY (^row22_kw_initialized residual seed Gu tu) kept`
             mp_tac))))))))) row22_omitted_seed_path_mods
         end) >>
        disch_then (qspecl_then [`src_tops`,`src`,
           `\(H:(bool # bytes32 # type_value) list # num list). cx_dead H cx`] mp_tac) >>
        BETA_TAC >>
        (impl_tac >-
          (qpat_assum `Abbrev (ce0 = _)`
            (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
           rpt conj_tac >>
           TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           (qpat_assum `~ce0.ce_is_ctor` mp_tac >> simp[NoAsms, Abbr `ce0`]))) >>
        disch_then (qx_choosel_then [`seed_D`,`seed_sites`,`seed_marks`,`seed_res`,`seed_G`,`seed_tn`]
          strip_assume_tac) >>
        `?entry reg_env registered. ci_mono sd entry /\
          entry.cs_current_bb = common.ec_common_label /\ entry.cs_current_insts = [] /\
          compile_register_positional_args (compile_register_kwarg_vars common.ec_env vars)
            common.ec_pos_args 4 entry = (reg_env,registered) /\ fn_has_code entry registered fn` by
          (qpat_assum `MEM (ExternalCommonJob common vars) jobs`
             (qx_choosel_then [`jp`,`jq`] assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
           `compile_external_jobs (jp ++ ExternalCommonJob common vars :: jq) sd = ((),sx)` by
             (qpat_assum `jobs = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
           `EVERY group_job_label_ok (jp ++ ExternalCommonJob common vars :: jq)` by
             (qpat_assum `jobs = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
           drule_all compile_external_common_job_interval >>
           disch_then (qx_choosel_then [`job_start`,`entry`,`reg_env`,`registered`,`done`] strip_assume_tac) >>
           qexistsl_tac [`entry`,`reg_env`,`registered`] >>
           conj_tac >-
             (irule exprLoweringPropsTheory.ci_mono_trans >> qexists `job_start` >>
              conj_tac >-
                (mp_tac (Q.SPECL [`jp`,`sd`] entryRejectAllocationIdsTheory.compile_external_jobs_ci_mono) >>
                 qpat_assum `compile_external_jobs jp sd = _` (fn eq => simp[NoAsms, eq])) >>
              mp_tac (Q.SPECL [`common.ec_common_label`,`job_start`] exprLoweringPropsTheory.ci_mono_new_block) >>
              qpat_assum `new_block common.ec_common_label job_start = _` (fn eq => simp[NoAsms, eq])) >>
           drule emitHelperPropsTheory.new_block_props >> strip_tac >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           irule entryCodeOwnershipTheory.fn_has_code_retained_interval >>
           conj_tac >- first_assum ACCEPT_TAC >> qexists `se` >>
           conj_tac >- first_assum ACCEPT_TAC >>
           irule cs_extends_trans >> qexists `done` >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           irule cs_extends_trans >> qexists `sx` >> conj_tac >> first_assum ACCEPT_TAC) >>
        `ci_mono cut sd` by
          (`ci_mono cut last` by
             (qpat_assum `emit_inst JMP _ [] cut = ((),last)` (fn eq =>
                qspecl_then [`JMP`,`[Label common.ec_common_label]`,`[]`,`cut`] mp_tac
                  exprLoweringPropsTheory.ci_mono_emit_inst >> simp[NoAsms, eq])) >>
           irule exprLoweringPropsTheory.ci_mono_trans >> qexists `last` >>
           conj_tac >- first_assum ACCEPT_TAC >>
           irule exprLoweringPropsTheory.ci_mono_trans >> qexists `dispatch_end` >>
           conj_tac >> first_assum ACCEPT_TAC) >>
        `sd.cs_next_id <= entry.cs_next_id /\ sd.cs_next_var <= entry.cs_next_var` by
          (qpat_assum `ci_mono sd entry` mp_tac >> simp[NoAsms, exprLoweringPropsTheory.ci_mono_def]) >>
        `cs_extends checks si` by
          (mp_tac (Q.INST [`st` |-> `checks`,`payable` |-> `common.ec_payable`,
                       `mincd` |-> `min_calldata_size common.ec_env pref 0`]
                     groupedEntryCountersTheory.compile_entry_checks_ci_mono) >>
           qpat_assum `compile_entry_checks _ _ checks = ((),si)` (fn eq =>
             simp[NoAsms, eq, exprLoweringPropsTheory.ci_mono_def])) >>
        `state_insts sf = []` by
          (qpat_assum `fresh_label "fallback" _ = (fl,sf)` mp_tac >>
           simp[NoAsms, fresh_label_def, initial_compile_state_def, state_insts_def, all_blocks_def] >>
           strip_tac >> simp[NoAsms] >> first_assum (SUBST1_TAC o SYM) >>
           simp[NoAsms, state_insts_def, all_blocks_def]) >>
        `fragFuel$no_phi_fn fn` by
          (simp[NoAsms, fragFuelTheory.no_phi_fn_def, EVERY_MEM] >> first_assum ACCEPT_TAC) >>
        `acyclic_struct_metadata common.ec_env.ce_struct_fields` by
          (qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
             (mp_then Any irule linkedEntryStructAcyclicTheory.checked_struct_metadata_acyclic_mods) >>
           qpat_assum `sfields_tenv_consistent ce0.ce_struct_fields (get_tenv cx)` mp_tac >>
           qpat_assum `get_tenv cx = _` (fn eq => simp[NoAsms, eq, Abbr `ce0`])) >>
        `EVERY (external_group_shape_mode_ok F) groups` by
          (simp[NoAsms, Abbr `groups`, EVERY_MAP] >>
           rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> qx_gen_tac `decl` >>
           disch_tac >> pop_assum kall_tac >>
           `external_fn_shape_mode_ok F (set_external_package_target rpolicy.rpol_target
              (package_external_fn_unit mods T (K global_nonreentrant_slot) decl))` by
             (PairCases_on `decl` >>
              qabbrev_tac `cenv = build_compile_env_unit mods decl0 External decl1 decl4 decl5 decl7 decl8 T` >>
              `cenv_static_mode_ok F cenv /\ (External <> Internal ==> cenv.ce_return_pc = NONE)` by
                (unabbrev_all_tac >> match_mp_tac build_compile_env_unit_static_mode >>
                 simp[expr_shape_root_mode_dynamic, EVERY_MEM, dynamic_raw_expr_shape]) >>
              Cases_on `decl7 = NoneT` >>
              gvs[package_external_fn_unit_def, set_external_package_target_def,
                  external_fn_shape_mode_ok_def, update_cenv_ret_abi_def,
                  update_cenv_nonreentrant_def, cenv_static_mode_ok_def,
                  expr_shape_root_mode_dynamic, dynamic_raw_stmt_shape] >>
              conj_tac >> first_assum ACCEPT_TAC) >>
           PairCases_on `decl` >>
           simp[package_external_group_unit_def] >> IF_CASES_TAC >> simp[]
           >- simp[external_group_shape_mode_ok_def, compute_selector_def, IS_PREFIX_APPEND] >>
           qmatch_asmsub_abbrev_tac `external_fn_shape_mode_ok F pkg` >>
           PairCases_on `pkg` >>
           fs[external_fn_shape_mode_ok_def, external_group_shape_mode_ok_def,
              external_common_shape_mode_ok_def, external_common_label_def,
              jump_label_ok_def, IS_PREFIX_APPEND] >>
           conj_tac
           >- simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD, external_prefix_label_def,
                   compute_selector_def, IS_PREFIX_APPEND] >>
           simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
                expr_shape_root_mode_dynamic, dynamic_raw_expr_shape]) >>
        `shape_state sd` by
          (`shape_state sf /\ compiler_label fl /\ label_sfx "fallback" fl` by
             (mp_tac (Q.SPECL [`F`,`jump_label_ok`,`\st. T`,`"fallback"`]
                        loweringShapeRulesTheory.shape_step_fresh_label_sfx) >>
              simp[NoAsms, shape_stable_def, shape_step_def] >>
              disch_then (qspecl_then [`initial_compile_state "__entry"`,`fl`,`sf`] mp_tac) >>
              qpat_assum `fresh_label "fallback" _ = (fl,sf)` (fn eq =>
                simp[NoAsms, eq, shape_state_initial_compile_state])) >>
           `jump_label_ok fl` by
             (qpat_assum `compiler_label fl` (fn label => simp[NoAsms, jump_label_ok_def, label])) >>
           `~label_sfx "dispatch" fl` by
             (strip_tac >> mp_tac (Q.INST [`s1` |-> `"fallback"`,`s2` |-> `"dispatch"`,
                        `l1` |-> `fl`,`l2` |-> `fl`] loweringShapeRulesTheory.label_sfx_distinct) >>
              simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC) >>
           mp_tac (Q.INST [`static` |-> `F`] compile_group_dispatch_linear_shape_mode) >>
           disch_then (qspecl_then [`groups`,`fl`] mp_tac) >>
           (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
           simp[NoAsms, shape_mode_step_def] >>
           disch_then (qspecl_then [`sf`,`jobs`,`sd`] mp_tac) >>
           (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
           strip_tac >> first_assum ACCEPT_TAC) >>
        qabbrev_tac `unknown_default_root = \z. case z of
          TopLevelName _ (owner,id) =>
            ~(declared_constant mods owner id \/ declared_immutable mods owner id)
          | _ => F` >>
        `!e. runtime_constant_expr mods e ==> ~supported_expr_exists unknown_default_root e` by
          (qpat_assum `Abbrev (unknown_default_root = _)` mp_tac >>
           rpt (pop_assum kall_tac) >> strip_tac >>
           `(!p e. p = unknown_default_root /\ runtime_constant_expr mods e ==>
                   ~supported_expr_exists p e) /\
            (!p t. p = unknown_default_root /\ F ==> ~supported_target_exists p t) /\
            (!p es. p = unknown_default_root /\ EVERY (runtime_constant_expr mods) es ==>
                   ~supported_exprs_exists p es) /\
            (!p opt. p = unknown_default_root /\ F ==> ~supported_opt_exists p opt) /\
            (!p fs. p = unknown_default_root /\ EVERY (runtime_constant_expr mods) (MAP SND fs) ==>
                   ~supported_fields_exists p fs)` by
             (ho_match_mp_tac supported_expr_exists_ind >>
              (rw[runtime_constant_expr_def, supported_expr_exists_def, Abbr `unknown_default_root`, FORALL_PROD] >-
                (qpat_assum `runtime_constant_expr mods (TopLevelName _ _)` mp_tac >>
                 rename1 `runtime_constant_expr _ (TopLevelName _ read_key) ==> _` >>
                 PairCases_on `read_key` >> fs[runtime_constant_expr_def])) >>
              fs[EVERY_MEM] >> metis_tac[whitelistCheckerConstsTheory.constant_expr_runtime_constant]) >>
           gen_tac >> disch_tac >>
           qpat_assum `!p e. p = unknown_default_root /\ runtime_constant_expr mods e ==> _` irule >> simp[]) >>
        `!owner id. declared_immutable mods owner id /\
          MEM (ReadAcc (StateRef (owner,id))) (accesses_exprs dflts) ==>
          ?i. FLOOKUP common.ec_env.ce_module_vars (owner,id) = SOME (ImmutableLoc i)` by
          (simp[NoAsms, declared_immutable_def, PULL_EXISTS] >> rpt strip_tac >>
           rename1 `MEM (VariableDecl vis Immutable id ty ini) itops` >>
           `ALOOKUP mods owner = SOME itops` by
             (irule ALOOKUP_ALL_DISTINCT_MEM >> conj_tac >> first_assum ACCEPT_TAC) >>
           qpat_assum `!read_key. MEM (ReadAcc (StateRef read_key)) (accesses_exprs dflts) ==> _`
             (drule_then strip_assume_tac) >>
           `mods = [(NONE,itops)] \/ linked_state_ref_allocated am.layouts tx.target mods (owner,id)` by
             (TRY (disj2_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
              qpat_assum `ALOOKUP mods owner = SOME itops` mp_tac >>
              qpat_assum `mods = [(NONE,_)]` (fn eq => simp[NoAsms, eq, AllCaseEqs()])) >>
           `?i. FLOOKUP ce0.ce_module_vars (owner,id) = SOME (ImmutableLoc i)` by
             (irule (INST_TYPE [``:'a`` |-> ``:160 word``, ``:'b`` |-> ``:num``]
                linked_owned_immutable_location) >>
              qexistsl [`tx.target`,`am.layouts`,`mods`,`ini`,`itops`,`ty`,`vis`] >>
              rpt conj_tac >>
              (first_assum ACCEPT_TAC ORELSE
               (disj1_tac >> first_assum ACCEPT_TAC) ORELSE
               (disj2_tac >> first_assum ACCEPT_TAC))) >>
           qpat_assum `FLOOKUP ce0.ce_module_vars (owner,id) = SOME (ImmutableLoc _)` mp_tac >>
           simp[NoAsms, Abbr `ce0`] >> strip_tac >> goal_assum drule) >>
        qabbrev_tac `bad_owned_default_root = \z. case z of
          TopLevelName _ (owner,id) =>
            (declared_constant mods owner id \/ declared_immutable mods owner id) /\
            ~(?i. FLOOKUP common.ec_env.ce_module_vars (owner,id) = SOME (ImmutableLoc i))
          | _ => F` >>
        `!e. MEM e ds ==> ~supported_expr_exists bad_owned_default_root e` by
          (gen_tac >> disch_tac >> strip_tac >>
           qpat_assum `!p P. (!z. p z ==> _) ==> _`
             (qspecl_then [`bad_owned_default_root`,
               `\(owner,id). (declared_constant mods owner id \/ declared_immutable mods owner id) /\
                 ~(?i. FLOOKUP common.ec_env.ce_module_vars (owner,id) = SOME (ImmutableLoc i))`] mp_tac) >>
           (impl_tac >- (Cases >> simp[NoAsms, Abbr `bad_owned_default_root`] >>
                         PairCases_on `p` >> simp[NoAsms])) >>
           disch_then (qspec_then `e` mp_tac) >>
           (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
           disch_then (qx_choose_then `read_key` strip_assume_tac) >>
           PairCases_on `read_key` >>
           qpat_x_assum `(\(own,nm). _) (read_key0,read_key1)`
             (mp_tac o CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)) >>
           disch_then (CONJUNCTS_THEN2 (DISJ_CASES_THEN assume_tac) mp_tac)
           >- (qpat_assum `declared_constant mods read_key0 read_key1`
                 (strip_assume_tac o REWRITE_RULE [declared_constant_def]) >>
               rename1 `MEM (VariableDecl _ (Constant _) read_key1 _ _) itops` >>
               `ALOOKUP mods read_key0 = SOME itops` by
                 (irule ALOOKUP_ALL_DISTINCT_MEM >> conj_tac >> first_assum ACCEPT_TAC) >>
               qpat_assum `!isrc ts v init id ty sl. _ ==> ALOOKUP _ _ <> NONE` mp_tac >>
               qpat_assum `ALOOKUP mods read_key0 = SOME itops` mp_tac >>
               qpat_assum `ALOOKUP (consts_env_mods mods) (read_key0,read_key1) = NONE` mp_tac >>
               qpat_assum `MEM (VariableDecl _ (Constant _) read_key1 _ _) itops` mp_tac >>
               rpt (pop_assum kall_tac) >> metis_tac[]) >>
           qpat_assum `!owner id. declared_immutable mods owner id /\ _ ==> _`
             (drule_all_then strip_assume_tac) >>
           qpat_assum `FLOOKUP common.ec_env.ce_module_vars (read_key0,read_key1) = SOME _`
             (fn eq => simp[NoAsms, eq])) >>
        qabbrev_tac `sha_root = \z. case z of Builtin _ Sha256 _ => T | _ => F` >>
        `(!e. no_sha256_expr e <=> ~supported_expr_exists sha_root e) /\
         (!bt. no_sha256_btarget bt <=> ~supported_target_exists sha_root bt) /\
         (!xs. no_sha256_exprs xs <=> ~supported_exprs_exists sha_root xs) /\
         (!opt. no_sha256_opt opt <=> ~supported_opt_exists sha_root opt) /\
         (!fs. no_sha256_fields fs <=> ~supported_fields_exists sha_root fs)` by
          (qpat_assum `Abbrev (sha_root = _)` mp_tac >> rpt (pop_assum kall_tac) >> disch_tac >>
           ho_match_mp_tac constSubstTheory.no_sha256_expr_ind >>
           simp[constSubstTheory.no_sha256_expr_def, supported_expr_exists_def, Abbr `sha_root`] >>
           rpt gen_tac >> CASE_TAC >> simp[]) >>
        `!e. MEM e ds ==> ~supported_expr_exists sha_root e` by
          (`!xs. supported_exprs_exists sha_root xs <=> EXISTS (supported_expr_exists sha_root) xs` by
             (rpt (pop_assum kall_tac) >> Induct >> simp[supported_expr_exists_def]) >>
           qpat_assum `no_sha256_exprs ds` mp_tac >>
           qpat_assum `!xs. no_sha256_exprs xs <=> _`
             (fn no_sha => qpat_assum `!xs. supported_exprs_exists sha_root xs <=> _`
               (fn exists_root => simp[NoAsms, no_sha, exists_root, EXISTS_MEM])) >>
           qpat_assum `no_sha256_exprs ds` kall_tac >>
           rpt (pop_assum kall_tac) >> metis_tac[]) >>
        qabbrev_tac `arity_root = \z. case z of
          Builtin _ b xs => ~builtin_args_length_ok b (LENGTH xs)
          | TypeBuiltin _ b _ xs => ~type_builtin_args_length_ok b (LENGTH xs)
          | _ => F` >>
        `!e. MEM e ds ==> ~supported_expr_exists arity_root e` by
          (`EVERY (well_typed_expr env) ds` by
             (qpat_assum `well_typed_exprs env ds` (ACCEPT_TAC o REWRITE_RULE [frame_well_typed_exprs_every])) >>
           gen_tac >> disch_tac >>
           `well_typed_expr env e` by
             (qpat_assum `EVERY (well_typed_expr env) ds` (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
           map_every assume_tac (CONJUNCTS runtimeDefaultCompileTheory.well_typed_expr_builtin_args_length) >>
           qpat_assum `!en x. well_typed_expr en x ==> ~supported_expr_exists _ x`
             (qspecl_then [`env`,`e`] mp_tac) >>
           qpat_assum `well_typed_expr env e` (fn typed => simp[NoAsms, typed, Abbr `arity_root`])) >>
        `!z. ^checked_default_expr common.ec_env z ==>
          unknown_default_root z \/ bad_owned_default_root z \/ sha_root z \/ arity_root z` by
          (simp[NoAsms, Abbr `unknown_default_root`, Abbr `bad_owned_default_root`,
                Abbr `sha_root`, Abbr `arity_root`] >>
           rpt (pop_assum kall_tac) >> Cases >> simp[]
           >- (PairCases_on `p` >> simp[] >> metis_tac[]) >>
           Cases_on `b` >> simp[]) >>
        `MAP (\(_,_,_,e). e) vars = ds` by
          (`LENGTH (DROP npos args) = LENGTH ds` by
             (qpat_assum `LENGTH ds <= LENGTH args` mp_tac >>
              qpat_assum `npos = LENGTH args - LENGTH ds` (fn eq => simp[NoAsms, eq, LENGTH_DROP])) >>
           qpat_assum `MAP _ vars = specs` (mp_tac o Q.AP_TERM `MAP (SND o SND)`) >>
           qpat_assum `specs = MAP _ _` (fn sp =>
             qpat_assum `LENGTH (DROP npos args) = LENGTH ds` (fn len =>
               simp[NoAsms, sp, MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, ETA_THM, MAP_ZIP, len]))) >>
        `EVERY (\(_,_,_,e). runtime_constant_expr mods e /\
                  ~supported_expr_exists (^checked_default_expr common.ec_env) e) vars` by
          (`EVERY (\e. runtime_constant_expr mods e /\
                    ~supported_expr_exists (^checked_default_expr common.ec_env) e) ds` suffices_by
             (qpat_assum `MAP (\(_,_,_,e). e) vars = ds` (SUBST1_TAC o SYM) >>
              simp[NoAsms, EVERY_MAP, combinTheory.o_DEF, ELIM_UNCURRY]) >>
           simp[NoAsms, EVERY_MEM] >> qx_gen_tac `e` >> disch_tac >>
           conj_asm1_tac >-
             (qpat_assum `EVERY (runtime_constant_expr mods) ds` (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
           strip_tac >>
           `supported_expr_exists
              (\z. unknown_default_root z \/ bad_owned_default_root z \/ sha_root z \/ arity_root z) e` by
             (irule (CONJUNCT1 supported_expr_exists_mono) >>
              qexists `^checked_default_expr common.ec_env` >> BETA_TAC >>
              conj_tac >- (first_assum (ACCEPT_TAC o BETA_RULE) ORELSE first_assum ACCEPT_TAC) >>
              simp[NoAsms] >> first_assum ACCEPT_TAC) >>
           `~supported_expr_exists unknown_default_root e /\
            ~supported_expr_exists bad_owned_default_root e /\
            ~supported_expr_exists sha_root e /\ ~supported_expr_exists arity_root e` by
             (rpt conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
           qpat_assum `supported_expr_exists (\z. _ \/ _) e` mp_tac >>
           qpat_assum `~supported_expr_exists unknown_default_root e` mp_tac >>
           qpat_assum `~supported_expr_exists bad_owned_default_root e` mp_tac >>
           qpat_assum `~supported_expr_exists sha_root e` mp_tac >>
           qpat_assum `~supported_expr_exists arity_root e` mp_tac >>
           simp[NoAsms, supported_expr_exists_disj]) >>
        `^row22_cut_facts unit.cu_context fn cut a entry` by
          (BETA_TAC >>
           let
             fun use pat k th = qpat_assum pat (mp_then Any k th)
           in
             (use `selected_registration_resources unit.cu_context fn ARB 0 si a` o
              use `compile_init_kwargs common.ec_env vars off k (Lit 0w) si = ((),cut)` o
              use `compile_init_kwargs common.ec_env vars off k (Lit 0w) si = ((),cut)` o
              use `compile_entry_checks (min_calldata_size common.ec_env pref 0) common.ec_payable checks = ((),si)` o
              use `compile_group_dispatch_linear groups fl sf = (jobs,sd)`)
               irule (BETA_RULE groupedRejectCutObserverTheory.row22_before_cut_certificate_count)
           end >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
           >- (qexists_tac `mods` >> first_assum (ACCEPT_TAC o BETA_RULE)) >>
           qexists_tac `se` >> conj_tac >> first_assum ACCEPT_TAC) >>
        Q.SUBGOAL_THEN
          `(?z J tj tags. z.vs_returndata = [] /\
              !D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[]) (a,Ga,ta) tags
                     (Abort Revert_abort z,J,tj)) \/
           (?w J tj tags. at_point cut w /\ fresh_vars_wrt entry w /\
              w.vs_call_ctx = a.vs_call_ctx /\
              (!id e. FLOOKUP w.vs_allocas id = SOME e ==> id < entry.cs_next_id) /\
              !D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[]) (a,Ga,ta) tags (OK w,J,tj))`
          (DISJ_CASES_THEN (qx_choosel_then [`w`,`J`,`tj`,`tags`]
                             (map_every assume_tac o CONJUNCTS)))
        >- (`!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[]) (a,Ga,ta) [] (OK u,Gu,tu)` by
              (qx_gen_tac `D` >> qpat_assum `!D exp. gas_origin_ptr_path _ (a,Ga,ta) [] (OK u,Gu,tu)`
                (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC)) >>
            qpat_x_assum `^row22_cut_facts unit.cu_context fn cut a entry`
              (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
            qpat_assum `!D. gas_origin_ptr_path _ (a,Ga,ta) [] (OK u,Gu,tu)`
              (mp_then Any irule (BETA_RULE row22_replay_initializer)) >>
            conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
            map_every qexists_tac [`seed_D`,`seed_sites`,`seed_marks`,`seed_res`,`seed_G`,`seed_tn`] >>
            qpat_assum `Abbrev (seed = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
            conj_tac >> first_assum ACCEPT_TAC)
        >- (map_every qexists_tac [`w`,`J`,`tj`,`tags`] >>
            conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `D` >>
            qpat_assum `!D exp. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK a,Ga,ta)`
              (qspecl_then [`D`,`EMPTY`] (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
            simp[NoAsms] >> disch_then irule >> first_assum (qspec_then `D` ACCEPT_TAC)) >>
        `!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
              (start,FEMPTY,entry_taint) tags (OK w,J,tj)` by
          (qx_gen_tac `D` >>
           qpat_assum `!D exp. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK a,Ga,ta)`
             (qspecl_then [`D`,`EMPTY`] (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
           simp[NoAsms] >> disch_then irule >> first_assum (qspec_then `D` ACCEPT_TAC)) >>
        `gas_path unit.cu_context fn start (LENGTH tags) (OK w)` by
          (qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) tags (OK w,J,tj)`
             (qspec_then `ARB` (mp_then Any ACCEPT_TAC bodyFullIfExpReachTheory.gas_origin_ptr_path_erase))) >>
        `~w.vs_halted` by drule_then (ACCEPT_TAC o CONJUNCT1) gas_path_normal >>
        `alloca_history fn start` by (irule alloca_history_empty >> conj_tac >> first_assum ACCEPT_TAC) >>
        `alloca_history fn w /\ alloca_inv w` by
          (qpat_assum `gas_path _ fn start _ (OK w)`
             (mp_then Any (qspec_then `w` mp_tac) rest_word_path_alloca) >>
           simp[NoAsms] >> disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `w.vs_initial_fmp = start.vs_initial_fmp /\
         w.vs_alloca_next + pending_alloca_size fn w =
         start.vs_alloca_next + pending_alloca_size fn start` by
          (qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) tags (OK w,J,tj)`
             (qspec_then `ARB` (mp_then Any irule decoder_origin_path_allocation_frame)) >>
           first_assum ACCEPT_TAC) >>
        `alloca_frontier_inv unit.cu_context fn ARB w` by
          (irule alloca_frontier_charge_frame >> qexists_tac `start` >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
        (* Obtain headroom on the real path from its checked edges, not from
           reachability in the cleared-outcome model. *)
        `o1_source_unit_ok unit` by
          (drule_all_then (ACCEPT_TAC o CONJUNCT1) lower_vyper_runtime_unit_source_unit_ok_mods) >>
        `!f. MEM f unit.cu_context.ctx_functions ==> pre_fmp_ops f` by
          (rpt strip_tac >> drule_all_then ACCEPT_TAC source_pre_fmp_ops) >>
        `pre_fmp_ops fn` by
          (qpat_assum `lookup_function "__entry" _ = SOME fn`
             (mp_then Any assume_tac lookup_function_MEM) >>
           qpat_assum `!f. MEM f _ ==> pre_fmp_ops f` irule >> first_assum ACCEPT_TAC) >>
        `!C f. ( !g. MEM g C.ctx_functions ==> pre_fmp_ops g) /\ pre_fmp_ops f /\
            ctx_has_dalloca C ==>
            !D lo xp PG x X tx0 ms y Y ty0.
              gas_origin_ptr_edge (D,lo,xp,C,f,PG) (x,X,tx0) ms (OK y,Y,ty0) ==>
              w2n x.vs_fmp <= w2n y.vs_fmp` by
          (rpt (pop_assum kall_tac) >> rpt gen_tac >> strip_tac >>
           `!fuel i x y. pre_fmp_opcode i.inst_opcode /\ dalloca_no_wrap i x /\
               step_inst fuel C i x = OK y ==> w2n x.vs_fmp <= w2n y.vs_fmp` by
             (rpt gen_tac >> strip_tac >> Cases_on `i.inst_opcode = DALLOCA`
              >- (gvs[dalloca_step_success, unitTransformDefsTheory.dalloca_no_wrap_def,
                       update_var_def] >>
                  `w2n x.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256)` by
                    (once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC) >>
                  simp[abiDecodeStaticPropsTheory.w2n_add_n2w_lt]) >>
              Cases_on `i.inst_opcode = INVOKE`
              >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
                  once_rewrite_tac[step_inst_def] >> simp[AllCaseEqs()] >> strip_tac >>
                  `pre_fmp_ops callee_fn` by metis_tac[lookup_function_MEM] >>
                  `ret.iret_adopt_fmp = NONE` by
                    (qpat_assum `run_blocks _ _ _ _ = IntRet _ _`
                       (mp_then Any irule (List.last (CONJUNCTS run_defs_adopt_fmp_none))) >>
                     first_assum ACCEPT_TAC) >>
                  drule (SIMP_RULE (srw_ss()) [update_var_def]
                    (Q.ISPEC `\s:venom_state. s.vs_fmp` bind_outputs_preserves)) >>
                  simp[adopt_return_fmp_def]) >>
              gvs[step_inst_non_invoke, pre_fmp_opcode_def] >>
              drule_all step_inst_base_OK_fmp_frame >> simp[]) >>
           rpt gen_tac >> disch_then (mp_then Any
             (CONJUNCTS_THEN2 assume_tac
               (qx_choosel_then [`fuel`,`bb`,`inst`,`middle`] (map_every assume_tac o CONJUNCTS)))
             gas_origin_ptr_edge_common_fuel) >>
           `MEM inst (fn_insts f)` by drule_all_then ACCEPT_TAC lookup_block_get_instruction_fn_insts >>
           `pre_fmp_opcode inst.inst_opcode` by
             (qpat_assum `pre_fmp_ops f` (mp_tac o REWRITE_RULE [pre_fmp_ops_def,EVERY_MEM]) >>
              disch_then drule >> simp[]) >>
           `dalloca_no_wrap inst x` by
             (Cases_on `inst.inst_opcode = DALLOCA`
              >- (qpat_assum `revert_forward_at _ _ \/ mem_safe_step _ _ _ _` strip_assume_tac
                  >- (drule_all revert_forward_at_opcode >> simp[]) >>
                  qpat_assum `mem_safe_step _ _ _ _`
                    (mp_tac o ONCE_REWRITE_RULE [mem_safe_step_def]) >> simp[]) >>
              simp[unitTransformDefsTheory.dalloca_no_wrap_def]) >>
           qpat_x_assum `(?_. middle = OK _ /\ _) \/ _` strip_assume_tac >>
           gvs[exit_result_def, jump_to_def] >>
           TRY (qpat_assum `eval_phis _ _ = OK _`
                  (mp_then Any SUBST1_TAC eval_phis_only_updates_vs_vars) >> simp[]) >>
           qpat_assum `!fuel i x y. _ ==> w2n x.vs_fmp <= w2n y.vs_fmp` irule >>
           map_every qexists_tac [`fuel`,`inst`] >> rpt conj_tac >>
           (first_assum ACCEPT_TAC ORELSE first_assum (ACCEPT_TAC o SYM))) >>
        `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
          case (cx,st,out) of ((D,lo,xp,C,f,PG),(x,X,tx0),(r,Y,ty0)) =>
            !y. r = OK y /\ (!g. MEM g C.ctx_functions ==> pre_fmp_ops g) /\
                pre_fmp_ops f /\ ctx_has_dalloca C ==> w2n x.vs_fmp <= w2n y.vs_fmp` by
          (qpat_x_assum `!C f. _ ==> !D lo xp PG x X tx0 ms y Y ty0. _`
             (fn th => rpt (pop_assum kall_tac) >> assume_tac th) >>
           ho_match_mp_tac gas_origin_ptr_path_ind >> simp[exit_result_def] >>
           rpt strip_tac >> gvs[exit_result_def] >>
           qpat_assum `!C f. _ ==> _` (qspecl_then [`ctx`,`func`] mp_tac) >>
           simp[] >> metis_tac[LESS_EQ_TRANS]) >>
        `ctx_has_dalloca unit.cu_context ==>
          allocas_below_fmp w /\ w.vs_alloca_next + pending_alloca_size fn w <= w2n w.vs_initial_fmp` by
          (strip_tac >>
           `w2n start.vs_fmp <= w2n w.vs_fmp` by
             (qpat_assum `!cx st ms out. gas_origin_ptr_path cx st ms out ==> _` (fn lift =>
                qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) tags (OK w,J,tj)`
                  (qspec_then `ARB` (mp_then Any mp_tac lift))) >>
              simp[NoAsms] >> disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
           `start.vs_initial_fmp = start.vs_fmp` by
             (qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
              simp[NoAsms, Abbr `start`, initial_venom_state_rel_mods_def]) >>
           `w.vs_alloca_next + pending_alloca_size fn w <= w2n w.vs_initial_fmp` by
             (qpat_assum `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp start /\ _`
                (drule_then strip_assume_tac) >>
              qpat_assum `w.vs_alloca_next + pending_alloca_size fn w = _` (SUBST1_TAC) >>
              qpat_assum `w.vs_initial_fmp = start.vs_initial_fmp` SUBST1_TAC >>
              first_assum ACCEPT_TAC) >>
           conj_tac >- (irule allocas_below_fmp_from_frontier >>
             conj_tac >- first_assum ACCEPT_TAC >>
             conj_tac
             >- (qpat_assum `w.vs_alloca_next + pending_alloca_size fn w <= _` mp_tac >>
                 decide_tac) >>
             qpat_assum `w.vs_initial_fmp = _` SUBST1_TAC >>
             qpat_assum `start.vs_initial_fmp = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
           first_assum ACCEPT_TAC) >>
        `?lbl pos m pay key' tr view rt.
           set_external_package_target rpolicy.rpol_target
             (package_external_fn_unit mods T (K global_nonreentrant_slot)
               (src,(mut,nr,rr,name,args,([]:expr list),ret,code))) =
               (lbl,common.ec_env,pos,m,pay,nr,key',tr,view,code,rt) /\
           common.ec_pos_args = build_positional_args common.ec_env (TAKE npos args)` by
          (qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _`
             (mp_tac o REWRITE_RULE [package_external_group_unit_def]) >>
           Cases_on `ret = NoneT` >>
           pop_assum (fn rt => qpat_assum `ds <> []` (fn ne =>
             simp[NoAsms, rt, ne, package_external_fn_unit_def, set_external_package_target_def,
                  LET_THM, NULL_EQ, compute_selector_method_id])) >>
           disch_then (map_every assume_tac o CONJUNCTS) >>
           qpat_assum `_ = common` (SUBST1_TAC o SYM) >>
           qpat_assum `LENGTH ds = LENGTH dflts` (fn eq => simp[NoAsms, Abbr `npos`, eq])) >>
        `params_ok (type_env_all_modules mods) args` by
          (qpat_assum `params_ok tenv args` mp_tac >> simp[NoAsms, Abbr `tenv`]) >>
        drule_all linked_registration_package_inputs >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        `LIST_REL (\(nm,ty) tv.
            abi_decoder_coherent common.ec_env tenv common.ec_env.ce_struct_fields ty tv /\
            (?loc. FLOOKUP common.ec_env.ce_vars nm = SOME loc /\
               var_location_memory_size loc = SOME (type_memory_size tv)) /\
            type_memory_size tv < dimword (:256)) args all_tvs` by
          (qpat_assum `?tvs. OPT_MMAP _ _ = SOME tvs /\ _`
             (qx_choose_then `full_tvs` strip_assume_tac) >>
           `full_tvs = all_tvs` by
             (qpat_assum `OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME all_tvs` mp_tac >>
              qpat_assum `OPT_MMAP (evaluate_type (type_env_all_modules mods)) _ = SOME full_tvs`
                (fn eq => simp[NoAsms, Abbr `tenv`, eq])) >>
           pop_assum SUBST_ALL_TAC >>
           `LENGTH args = LENGTH all_tvs` by
             (qpat_assum `OPT_MMAP (evaluate_type tenv) _ = SOME all_tvs`
                (mp_then Any mp_tac vyperTypeABITheory.OPT_MMAP_LENGTH) >> simp[NoAsms]) >>
           qpat_assum `LIST_REL _ args (ZIP _)` mp_tac >>
           qpat_assum `LENGTH args = LENGTH all_tvs` (fn eq =>
             simp[NoAsms, Abbr `tenv`, GSYM eq, LIST_REL_EL_EQN, LENGTH_ZIP, LENGTH_MAP]) >>
           disch_then strip_assume_tac >> qx_gen_tac `n` >> strip_tac >>
           qpat_assum `!n. n < LENGTH args ==> _ (EL n args) (EL n (ZIP _))`
             (qspec_then `n` mp_tac) >>
           Cases_on `EL n args` >>
           qpat_assum `n < LENGTH args` (fn lt =>
             qpat_assum `LENGTH args = LENGTH all_tvs` (fn len =>
               qpat_assum `EL n args = _` (fn el =>
                 simp[NoAsms, lt, GSYM len, EL_ZIP, EL_MAP, LENGTH_MAP, el])))) >>
        `MAP (\(name,_,_,_). name) vars = MAP FST (DROP npos args)` by
          (qpat_assum `npos = LENGTH args - LENGTH ds` SUBST1_TAC >>
           drule_all_then ACCEPT_TAC callRejectMemoryTheory.grouped_kwarg_names) >>
        drule_all callRejectMemoryTheory.registered_kwarg_positional_metadata >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        `TAKE npos tvs = pos_tvs` by
          (simp[NoAsms, Abbr `tvs`, Abbr `pos_tvs`, rich_listTheory.TAKE_TAKE_T]) >>
        `SUM (MAP tv_abi_size pos_tvs) <= SUM (MAP tv_abi_size tvs)` by
          (qpat_assum `TAKE npos tvs = pos_tvs` (SUBST1_TAC o SYM) >>
           irule callRejectMemoryTheory.prefix_head_size_le) >>
        `4 + SUM (MAP tv_abi_size pos_tvs) <= LENGTH cd` by
          (qpat_assum `SUM (MAP tv_abi_size pos_tvs) <= _` mp_tac >>
           qpat_assum `4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd` mp_tac >> decide_tac) >>
        `allocas_from 0 w` by simp[NoAsms, allocas_from_def] >>
        `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp w` by
          (qpat_assum `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp w /\ _` mp_tac >>
           simp[NoAsms]) >>
        qabbrev_tac `at_entry = jump_to entry.cs_current_bb w` >>
        `at_point entry at_entry /\
         !D exp. gas_origin_ptr_path (D,0,exp,unit.cu_context,fn,[])
             (w,J,tj) [] (OK at_entry,J,tj)` by
          (simp[NoAsms, Abbr `at_entry`] >>
           mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `PG` |-> `[]`,
                           `lo` |-> `0`, `G` |-> `J`, `tn` |-> `tj`,
                           `s` |-> `w`, `st` |-> `entry`, `term` |-> `last`]
                    grouped_entry_jump_to_common) >>
           (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
             qpat_assum `entry.cs_current_bb = _` SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
           disch_then ACCEPT_TAC) >>
        `at_entry.vs_call_ctx.cc_calldata = cd` by
          (qpat_assum `w.vs_call_ctx = a.vs_call_ctx` (fn cc =>
             qpat_assum `a.vs_call_ctx.cc_calldata = cd` (fn cd_eq =>
               simp[NoAsms, Abbr `at_entry`, jump_to_def, cc, cd_eq]))) >>
        `LENGTH at_entry.vs_call_ctx.cc_calldata < dimword (:256)` by
          (qpat_assum `LENGTH a.vs_call_ctx.cc_calldata < _` mp_tac >>
           qpat_assum `a.vs_call_ctx.cc_calldata = cd` (fn ac =>
             qpat_assum `at_entry.vs_call_ctx.cc_calldata = cd` (fn wc => simp[NoAsms, ac,wc]))) >>
        `alloca_inv at_entry /\ alloca_frontier_inv unit.cu_context fn ARB at_entry` by
          (mp_tac (Q.INST [`t` |-> `at_entry`, `s` |-> `w`, `site` |-> `ARB`,
                           `ctx` |-> `unit.cu_context`]
                    decoderCalldataShellTheory.calldata_alloca_invariants_fields) >>
           (impl_tac >- simp[NoAsms, Abbr `at_entry`, jump_to_def]) >>
           strip_tac >> rpt conj_tac >> (first_assum (irule o iffRL)) >> first_assum ACCEPT_TAC) >>
        `ctx_has_dalloca unit.cu_context ==>
           allocas_below_fmp at_entry /\
           at_entry.vs_alloca_next + pending_alloca_size fn at_entry <= w2n at_entry.vs_initial_fmp` by
          (strip_tac >> qpat_assum `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp w /\ _`
             (drule_then strip_assume_tac) >>
           conj_tac >-
             (mp_tac (Q.INST [`t` |-> `at_entry`, `s` |-> `w`]
                        allocasBelowFmpUpdatesPropsTheory.allocas_below_fmp_fields) >>
              (impl_tac >- simp[NoAsms, Abbr `at_entry`, jump_to_def]) >>
              disch_then (irule o iffRL) >> first_assum ACCEPT_TAC) >>
           qpat_assum `w.vs_alloca_next + pending_alloca_size fn w <= _` mp_tac >>
           simp[NoAsms, Abbr `at_entry`, jump_to_def, exprLoweringPropsTheory.pending_alloca_size_def]) >>
        `(!id e. FLOOKUP at_entry.vs_allocas id = SOME e ==> id < entry.cs_next_id) /\
         fresh_vars_wrt entry at_entry /\ ~at_entry.vs_halted /\
         at_entry.vs_current_bb = entry.cs_current_bb /\
         at_entry.vs_inst_idx = LENGTH entry.cs_current_insts` by
          (qpat_assum `at_point entry at_entry` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           simp[NoAsms, Abbr `at_entry`, jump_to_def, fresh_vars_wrt_def] >>
           TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
           qpat_assum `fresh_vars_wrt entry w` (ACCEPT_TAC o REWRITE_RULE [fresh_vars_wrt_def])) >>
        `compile_register_positional_args (compile_register_kwarg_vars common.ec_env vars)
           (build_positional_args (compile_register_kwarg_vars common.ec_env vars) (TAKE npos args))
           4 entry = (reg_env,registered)` by
          (qpat_assum `build_positional_args (compile_register_kwarg_vars _ _) _ = _` SUBST1_TAC >>
           qpat_assum `common.ec_pos_args = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
        `LIST_REL (\(nm,ty) tv.
            abi_decoder_coherent (compile_register_kwarg_vars common.ec_env vars) tenv
              (compile_register_kwarg_vars common.ec_env vars).ce_struct_fields ty tv /\
            (?loc. FLOOKUP (compile_register_kwarg_vars common.ec_env vars).ce_vars nm = SOME loc /\
               var_location_memory_size loc = SOME (type_memory_size tv)) /\
            type_memory_size tv < dimword (:256)) (TAKE npos args) pos_tvs` by
          (qpat_assum `LIST_REL _ (TAKE npos args) (TAKE npos all_tvs)` mp_tac >>
           simp[NoAsms, Abbr `pos_tvs`, Abbr `tvs`, rich_listTheory.TAKE_TAKE_T]) >>
        `4 + SUM (MAP tv_abi_size pos_tvs) <= LENGTH at_entry.vs_call_ctx.cc_calldata /\
         calldata_decode_args at_entry.vs_call_ctx.cc_calldata pos_tvs 0 = NONE` by
          (qpat_assum `at_entry.vs_call_ctx.cc_calldata = cd` SUBST1_TAC >>
           conj_tac >> first_assum ACCEPT_TAC) >>
        mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `env` |-> `tenv`, `site` |-> `ARB`,
                        `s` |-> `at_entry`, `tvs` |-> `pos_tvs`, `G` |-> `J`, `tn` |-> `tj`,
                        `args` |-> `TAKE npos args`, `sa` |-> `entry`,
                        `ce` |-> `compile_register_kwarg_vars common.ec_env
                                     (vars:(string # operand # type # expr) list)`,
                        `cef` |-> `reg_env`, `sb` |-> `registered`]
                  callRejectMemoryTheory.coherent_registration_reject_path) >>
        (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
          rpt gen_tac >> strip_tac >>
          qpat_assum `!label bb. lookup_block label _ = SOME bb ==> _` (drule_then ACCEPT_TAC))) >>
        disch_then (qx_choosel_then [`z`,`H`,`tz`] strip_assume_tac) >>
        qexistsl_tac [`z`,`H`,`tz`,`tags`] >> conj_tac >- first_assum ACCEPT_TAC >>
        qx_gen_tac `D` >>
        qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) tags (OK w,J,tj)`
          (qspec_then `D` (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
        disch_then (qspecl_then [`w`,`J`,`tj`,`[]`,`Abort Revert_abort z`,`H`,`tz`] mp_tac) >>
        simp[NoAsms] >> disch_then irule >>
        qpat_assum `!D exp. gas_origin_ptr_path _ (w,J,tj) [] (OK at_entry,J,tj)`
          (qspecl_then [`D`,`EMPTY`] (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
        simp[NoAsms] >> disch_then irule >>
        first_assum (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC)) >>
        qpat_assum `_ ==> ?z J tz. z.vs_returndata = [] /\ _`
          (mp_tac) >>
        (impl_tac >- (disj1_tac >> qpat_assum `~(common.ec_payable \/ _)` mp_tac >> simp[NoAsms])) >>
        disch_then (qx_choosel_then [`z`,`J`,`tz`] strip_assume_tac) >>
        qexistsl_tac [`z`,`J`,`tz`,`[]`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `start.vs_call_ctx.cc_calldata = cd` by
        (qpat_assum `start.vs_call_ctx = _` (fn eq => simp[NoAsms, eq, Abbr `cd`])) >>
      Cases_on `(~common.ec_payable /\ start.vs_call_ctx.cc_callvalue <> 0w) \/
        (4 < min_calldata_size common.ec_env pref 0 /\
         LENGTH start.vs_call_ctx.cc_calldata < min_calldata_size common.ec_env pref 0)`
      >- (qpat_assum `_ ==> ?z J tz. z.vs_returndata = [] /\ _` (drule_then
            (qx_choosel_then [`z`,`J`,`tz`] strip_assume_tac)) >>
          qexistsl_tac [`z`,`J`,`tz`,`[]`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      (Q.SUBGOAL_THEN
        `min_calldata_size common.ec_env pref 0 <= LENGTH start.vs_call_ctx.cc_calldata /\
         (common.ec_payable \/ start.vs_call_ctx.cc_callvalue = 0w)`
        (map_every assume_tac o CONJUNCTS) >-
        (qpat_assum `~((~common.ec_payable /\ _) \/ _)` mp_tac >>
         qpat_assum `4 <= LENGTH start.vs_call_ctx.cc_calldata` mp_tac >>
         qpat_assum `min_calldata_size common.ec_env pref 0 = _` (fn mc => simp[NoAsms, mc]) >>
         decide_tac)) >>
      `calldata_decode_args start.vs_call_ctx.cc_calldata kw_tvs
         (SUM (MAP tv_abi_size pos_tvs)) = NONE` by
        (qpat_assum `LENGTH cd < _ \/ calldata_decode_args cd kw_tvs _ = NONE` mp_tac >>
         qpat_assum `min_calldata_size common.ec_env pref 0 <= _` mp_tac >>
         qpat_assum `min_calldata_size common.ec_env pref 0 = _` (fn mc =>
           qpat_assum `start.vs_call_ctx.cc_calldata = cd` (fn cc => simp[NoAsms, mc, cc]))) >>
      `pos_tvs = TAKE npos all_tvs /\ kw_tvs = TAKE k (DROP npos all_tvs)` by
        simp[NoAsms, Abbr `pos_tvs`, Abbr `kw_tvs`, Abbr `tvs`,
             rich_listTheory.TAKE_TAKE_T, DROP_TAKE] >>
      `LENGTH kw_tvs = k` by
        (`LENGTH args = LENGTH all_tvs` by
           (qpat_assum `OPT_MMAP (evaluate_type tenv) _ = SOME all_tvs`
              (mp_then Any mp_tac vyperTypeABITheory.OPT_MMAP_LENGTH) >> simp[NoAsms]) >>
         qpat_assum `kw_tvs = TAKE k _` SUBST1_TAC >>
         `k <= LENGTH (DROP npos all_tvs)` by
           (simp[NoAsms, LENGTH_DROP, Abbr `npos`] >>
            qpat_assum `LENGTH args = LENGTH all_tvs` (SUBST1_TAC o SYM) >>
            qpat_assum `LENGTH ds = LENGTH dflts` (SUBST1_TAC o SYM) >>
            qpat_assum `LENGTH ds <= LENGTH args` mp_tac >>
            qpat_assum `k <= LENGTH dflts` mp_tac >>
            qpat_assum `LENGTH ds = LENGTH dflts` (SUBST1_TAC o SYM) >> decide_tac) >>
         qpat_assum `k <= LENGTH (DROP _ _)` mp_tac >>
         simp[NoAsms, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF]) >>
      `off = 4 + SUM (MAP tv_abi_size pos_tvs)` by
        (qpat_assum `off = min_calldata_size _ _ _` SUBST1_TAC >>
         qpat_assum `pos_tvs = TAKE _ _` SUBST1_TAC >>
         irule groupedDefaultArgumentsTheory.grouped_argument_min_calldata_size >>
         qexists_tac `tenv` >> first_assum ACCEPT_TAC) >>
      `4 + SUM (MAP tv_abi_size pos_tvs) + SUM (MAP tv_abi_size kw_tvs) < dimword (:256)` by
        (`pos_tvs ++ kw_tvs = tvs` by simp[NoAsms, Abbr `pos_tvs`, Abbr `kw_tvs`, TAKE_DROP] >>
         qpat_assum `min_calldata_size common.ec_env pref 0 < _` mp_tac >>
         qpat_assum `min_calldata_size common.ec_env pref 0 = _` SUBST1_TAC >>
         qpat_assum `pos_tvs ++ kw_tvs = tvs` (SUBST1_TAC o SYM) >>
         pure_rewrite_tac[MAP_APPEND, SUM_APPEND, arithmeticTheory.ADD_ASSOC] >>
         disch_then ACCEPT_TAC) >>
      `!vars st t H u.
        MAP (\(n,_,ty,e). (n,ty,e)) vars = specs /\
        (!name op ty e. MEM (name,op,ty,e) vars ==>
          ?dst d oid. op = Var dst /\ not_fresh_at st dst /\ lookup_var dst t = SOME (n2w d) /\
            ptr_covers H u dst t (type_memory_bytes common.ec_env ty) /\
            FLOOKUP t.vs_allocas oid = SOME (d,type_memory_bytes common.ec_env ty) /\
            d + type_memory_bytes common.ec_env ty < dimword (:256)) ==>
        LIST_REL (supplied_keyword_owner common.ec_env tenv st t H u) (TAKE k vars) kw_tvs` by
        (rpt gen_tac >> strip_tac >>
         `LIST_REL (\(nm,ty) tv. abi_decoder_coherent common.ec_env tenv common.ec_env.ce_struct_fields ty tv)
            args all_tvs` by
           (qpat_assum `LIST_REL (\arg tv. abi_decoder_coherent _ _ _ (SND arg) tv) args all_tvs`
              mp_tac >> simp[NoAsms, pairTheory.LAMBDA_PROD]) >>
         `npos = LENGTH args - LENGTH ds` by
           (qpat_assum `LENGTH ds = LENGTH dflts` (fn eq => simp[NoAsms, eq, Abbr `npos`])) >>
         `k <= LENGTH ds` by
           (qpat_assum `LENGTH ds = LENGTH dflts` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         qpat_assum `kw_tvs = TAKE k _` SUBST1_TAC >>
         qpat_assum `specs = MAP _ _` SUBST_ALL_TAC >>
         `LENGTH (TAKE k (DROP npos all_tvs)) = k /\
          LIST_REL (supplied_keyword_owner common.ec_env tenv st t H u) (TAKE k vars)
            (TAKE k (DROP npos all_tvs))` suffices_by simp[NoAsms] >>
         irule groupedKeywordRejectTheory.grouped_supplied_owners >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`args`,`ds`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         qpat_assum `npos = LENGTH args - LENGTH ds` SUBST1_TAC >>
         first_assum ACCEPT_TAC) >>
      qpat_assum `off = 4 + _` SUBST_ALL_TAC >>
      drule_all groupedKeywordRejectTheory.grouped_bad_supplied_origin >>
      disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
        (qx_choosel_then [`z`,`J`,`tz`] strip_assume_tac)) >>
      qexistsl_tac [`z`,`J`,`tz`,`[]`] >> conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `D` >> first_assum (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC)) >>
      (* A selected group without defaults uses the installed legacy job. *)
      `pref = args /\ k = 0` by
        (qpat_assum `MEM (pref,k) (abi_entries args dflts)` mp_tac >>
         qpat_assum `dflts = []` SUBST1_TAC >> simp[NoAsms, abi_entries_no_defaults]) >>
      `tvs = all_tvs` by
        (qpat_assum `OPT_MMAP (evaluate_type tenv) tys = SOME tvs` mp_tac >>
         qpat_assum `tys = MAP SND pref` SUBST1_TAC >>
         qpat_assum `pref = args` SUBST1_TAC >> simp[]) >>
      qabbrev_tac `code = subst_consts_stmts_mods (consts_env_mods mods) rawbody` >>
      `key = (src,mut,nr,rr,name,args,([]:expr list),ret,code)` by
        simp[Abbr `key`, Abbr `code`, subst_consts_fn_mods_def, subst_consts_expr_mods_def] >>
      `fn_allocs_ok_unit mods key` by
        (qpat_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
         qpat_assum `classify_functions_unit _ _ = _` (fn eq =>
           simp[NoAsms, lower_vyper_runtime_unit_mods_def, LET_THM,
                eq, AllCaseEqs(), EVERY_APPEND, EVERY_MEM]) >>
         rpt strip_tac >> first_x_assum (drule_then ACCEPT_TAC)) >>
      `contract_namespaces_ok F mods` by
        (qpat_assum `source_typing_ok_mods _ _ _ _` mp_tac >>
         simp[NoAsms, source_typing_ok_mods_def] >> strip_tac >>
         drule_then ACCEPT_TAC vyperTypeContractContextTheory.check_contract_namespaces_ok) >>
      `?lbl ce pos mc pay nk tr view rt.
        set_external_package_target rpolicy.rpol_target
          (package_external_fn_unit mods T (K global_nonreentrant_slot) key) =
        (lbl,ce,pos,mc,pay,nr,nk,tr,view,code,rt)` by
        (qpat_assum `key = (src,mut,nr,rr,name,args,[],ret,code)` SUBST1_TAC >>
         Cases_on `ret = NoneT` >>
         simp[NoAsms, set_external_package_target_def, package_external_fn_unit_def]) >>
      `fn_allocs_ok_unit mods (src,mut,nr,rr,name,args,([]:expr list),ret,code) /\
       set_external_package_target rpolicy.rpol_target
          (package_external_fn_unit mods T (K global_nonreentrant_slot)
             (src,mut,nr,rr,name,args,([]:expr list),ret,code)) =
         (lbl,ce,pos,mc,pay,nr,nk,tr,view,code,rt)` by
        (qpat_assum `key = (src,mut,nr,rr,name,args,[],ret,code)` (SUBST1_TAC o SYM) >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      `params_ok (type_env_all_modules mods) args` by
        (qpat_assum `params_ok tenv args` mp_tac >> simp[NoAsms, Abbr `tenv`]) >>
      drule_all linked_registration_package_inputs >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `?xs. OPT_MMAP (evaluate_type (type_env_all_modules mods)) (MAP SND args) = SOME xs /\ _`
        (qx_choose_then `pkg_tvs` (map_every assume_tac o CONJUNCTS)) >>
      `pkg_tvs = tvs` by
        (qpat_assum `OPT_MMAP (evaluate_type (type_env_all_modules mods)) (MAP SND args) = SOME pkg_tvs` mp_tac >>
         qpat_assum `OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME all_tvs` mp_tac >>
         qpat_assum `tvs = all_tvs` SUBST1_TAC >> simp[NoAsms, Abbr `tenv`]) >>
      qpat_assum `pkg_tvs = tvs` SUBST_ALL_TAC >>
      `LIST_REL (\(nm,ty) tv.
          abi_decoder_coherent ce tenv ce.ce_struct_fields ty tv /\
          (?loc. FLOOKUP ce.ce_vars nm = SOME loc /\
            var_location_memory_size loc = SOME (type_memory_size tv)) /\
          type_memory_size tv < dimword (:256)) args tvs` by
        (`LENGTH args = LENGTH tvs` by
           (qpat_assum `OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME all_tvs`
              (mp_then Any mp_tac vyperTypeABITheory.OPT_MMAP_LENGTH) >> simp[]) >>
         qpat_assum `LIST_REL _ args (ZIP (MAP SND args,tvs))` mp_tac >>
         qpat_assum `LENGTH args = LENGTH tvs` (fn eq =>
           simp[NoAsms, Abbr `tenv`, GSYM eq, LIST_REL_EL_EQN, LENGTH_ZIP, LENGTH_MAP]) >>
         disch_then strip_assume_tac >> qx_gen_tac `i` >> strip_tac >>
         qpat_assum `!i. i < LENGTH args ==> _ (EL i args) (EL i (ZIP _))`
           (qspec_then `i` mp_tac) >>
         Cases_on `EL i args` >>
         qpat_assum `i < LENGTH args` (fn lt =>
           qpat_assum `LENGTH args = LENGTH tvs` (fn len =>
             qpat_assum `EL i args = _` (fn el =>
               simp[NoAsms, lt, GSYM len, EL_ZIP, EL_MAP, LENGTH_MAP, el])))) >>
      qabbrev_tac `pk = (lbl,ce,pos,mc,pay,nr,nk,tr,view,code,rt)` >>
      `grp = ExternalSingle (cd_selector cd,lbl,selector_has_trailing_zeroes (cd_selector cd)) pk` by
        (`abi_method_id (type_env_all_modules mods) name (MAP SND args) = cd_selector cd` by
           (qpat_assum `abi_method_id tenv name tys = _` mp_tac >>
            qpat_assum `tys = MAP SND pref` SUBST1_TAC >>
            qpat_assum `pref = args` SUBST1_TAC >> simp[NoAsms, Abbr `tenv`]) >>
         simp[NoAsms, Abbr `grp`] >>
         qpat_assum `key = (src,mut,nr,rr,name,args,[],ret,code)` SUBST1_TAC >>
         qpat_assum `set_external_package_target _
            (package_external_fn_unit _ _ _ (src,mut,nr,rr,name,args,[],ret,code)) = _` (fn eq =>
           qpat_assum `abi_method_id (type_env_all_modules mods) name (MAP SND args) = cd_selector cd`
             (fn sel => qpat_assum `lbl = "fn_" ++ name` (fn lab =>
               simp[NoAsms, package_external_group_unit_def, LET_THM, eq, sel, lab,
                    selectorCompilerPropsTheory.compute_selector_method_id])))) >>
      `calldata_method_id start.vs_call_ctx.cc_calldata = n2w (cd_selector cd)` by
        (qpat_assum `cd_selector cd = w2n _` (fn eq => simp[NoAsms, eq])) >>
      drule_all grouped_dispatch_long_prelude_with_frame >>
      disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
        (qx_choosel_then [`mid`,`prep`,`cut`,`cut_block`,`before`,`Gb`,`tb`]
           (map_every assume_tac o CONJUNCTS))) >>
      `groups = pre ++ ExternalSingle
         (cd_selector cd,lbl,selector_has_trailing_zeroes (cd_selector cd)) pk::post` by
        (qpat_assum `grp = ExternalSingle _ _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      qpat_assum `groups = pre ++ ExternalSingle _ _ :: post` SUBST_ALL_TAC >>
      drule_all compile_external_groups_selected_single_origin >>
      disch_then (qspecl_then [`[]`,`Gb`]
        (qx_choosel_then [`prefix_jobs`,`cmp`,`cmpend`,`hit`,`Gh`,`th`]
           (map_every assume_tac o CONJUNCTS))) >>
      drule_all compile_external_legacy_job_interval >>
      disch_then (qx_choosel_then [`legacy_begin`,`legacy_end`,`jobs_pre`,`jobs_post`]
        (map_every assume_tac o CONJUNCTS)) >>
      `MEM (lbl,ce,pos,mc,pay,nr,nk,tr,view,code,rt) [pk]` by simp[NoAsms, Abbr `pk`] >>
      drule_all entryCompileIntervalsTheory.external_fn_selected_check_intervals >>
      disch_then (qx_choosel_then [`opened`,`checked`,`cef`,`registered`,`bodyend`] strip_assume_tac) >>
      `ci_mono checked registered` by
        (qpat_assum `compile_register_positional_args ce pos 4 checked = _` (fn eq =>
           mp_tac (Q.SPECL [`pos`,`ce`,`4`,`checked`]
             calldataRegistrationExecTheory.registration_compile_ci_mono) >> simp[NoAsms, eq])) >>
      `cs_extends checked registered` by
        (qpat_assum `ci_mono checked registered` mp_tac >> simp[NoAsms, exprLoweringPropsTheory.ci_mono_def]) >>
      `cs_extends registered legacy_end` by
        (irule cs_extends_trans >> qexists_tac `bodyend` >> conj_tac >> first_assum ACCEPT_TAC) >>
      `cs_extends legacy_begin checked` by
        (irule cs_extends_trans >> qexists_tac `opened` >> conj_tac >> first_assum ACCEPT_TAC) >>
      `fn_has_code opened checked fn /\ fn_has_code checked registered fn` by
        (qpat_assum `fn_has_code legacy_begin legacy_end fn`
           (mp_then Any assume_tac fn_has_code_mid) >>
         conj_tac >> first_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `EVERY group_entry_labels_ok post` by
        (qpat_assum `EVERY group_entry_labels_ok (pre ++ ExternalSingle _ _ :: post)` mp_tac >>
         simp[NoAsms, EVERY_APPEND]) >>
      drule_all compile_external_groups_append_layout >>
      disch_then (qx_choosel_then [`early_jobs`,`tail_jobs`,`split_at`] strip_assume_tac) >>
      `split_at = cmp` by
        (qpat_assum `compile_external_groups (Var mid) pre prep = (early_jobs,split_at)` mp_tac >>
         qpat_assum `compile_external_groups (Var mid) pre prep = (prefix_jobs,cmp)`
           (fn eq => simp[NoAsms, eq])) >>
      qpat_assum `split_at = cmp` SUBST_ALL_TAC >>
      drule_all compile_external_single_cons_layout >>
      disch_then (qx_choosel_then [`later`,`remaining`] strip_assume_tac) >>
      `later = cmpend` by
        (qpat_assum `compile_selector_checks (Var mid) _ cmp = ((),later)` mp_tac >>
         qpat_assum `compile_selector_checks (Var mid) _ cmp = ((),cmpend)`
           (fn eq => simp[NoAsms, eq])) >>
      qpat_assum `later = cmpend` SUBST_ALL_TAC >>
      `ci_mono cmpend cut` by
        (`cut = SND (compile_external_groups (Var mid) post cmpend)` by
           (qpat_assum `compile_external_groups (Var mid) post cmpend = _`
              (fn eq => simp[NoAsms, eq])) >>
         pop_assum SUBST1_TAC >> irule groupedEntryCountersTheory.compile_external_groups_ci_mono) >>
      `ci_mono cmp cmpend` by
        (`cmpend = SND (compile_selector_checks (Var mid) [(cd_selector cd,lbl)] cmp)` by
           (qpat_assum `compile_selector_checks (Var mid) _ cmp = ((),cmpend)`
              (fn eq => simp[NoAsms, eq])) >>
         pop_assum SUBST1_TAC >> irule groupedEntryCountersTheory.compile_selector_checks_ci_mono) >>
      `ci_mono sd legacy_begin` by
        (mp_tac (Q.SPECL [`jobs_pre`,`sd`] entryRejectAllocationIdsTheory.compile_external_jobs_ci_mono) >>
         qpat_assum `compile_external_jobs jobs_pre sd = _` (fn eq => simp[NoAsms, eq])) >>
      `ci_mono legacy_begin opened` by
        (`pre' = []` by
           (qpat_assum `[pk] = pre' ++ _` mp_tac >> Cases_on `pre'` >> simp[NoAsms]) >>
         `before' = legacy_begin` by
           (qpat_assum `compile_external_fn_bodies pre' legacy_begin = _` mp_tac >>
            qpat_assum `pre' = []` SUBST1_TAC >>
            simp[NoAsms, compile_external_fn_bodies_def, comp_return_def]) >>
         mp_tac (Q.SPECL [`lbl`,`legacy_begin`] exprLoweringPropsTheory.ci_mono_new_block) >>
         qpat_assum `before' = legacy_begin` SUBST_ALL_TAC >>
         qpat_assum `new_block lbl legacy_begin = _` (fn eq => simp[NoAsms, eq])) >>
      `ci_mono cmpend opened` by
        (irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `cut` >>
         conj_tac >- first_assum ACCEPT_TAC >>
         irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `sd` >>
         conj_tac >- first_assum ACCEPT_TAC >>
         irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `legacy_begin` >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      `fresh_vars_wrt opened hit` by
        (irule emitHelperPropsTheory.fresh_vars_wrt_mono >> qexists_tac `cmpend` >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         qpat_assum `ci_mono cmpend opened` mp_tac >>
         simp[NoAsms, exprLoweringPropsTheory.ci_mono_def]) >>
      `selected_registration_resources unit.cu_context fn ARB 0 opened hit` by
        (qpat_assum `opened.cs_current_bb = lbl` (fn bb =>
           qpat_assum `opened.cs_current_insts = []` (fn insts =>
             simp[NoAsms, selected_registration_resources_def, bb, insts])) >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         rpt strip_tac >>
         `id < cmp.cs_next_id` by
           (qpat_assum `!id entry. FLOOKUP hit.vs_allocas id = SOME entry ==> id < cmp.cs_next_id`
              (qspecl_then [`id`,`entry`] mp_tac) >> simp[]) >>
         qpat_assum `ci_mono cmp cmpend` mp_tac >> qpat_assum `ci_mono cmpend opened` mp_tac >>
         simp[NoAsms, exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
      `hit.vs_call_ctx = start.vs_call_ctx` by
        (qpat_assum `selected_registration_frame before tb hit th` mp_tac >>
         qpat_assum `selected_registration_frame start entry_taint before tb` mp_tac >>
         simp[NoAsms, selected_registration_frame_def]) >>
      `hit.vs_call_ctx.cc_calldata = cd` by
        (qpat_assum `hit.vs_call_ctx = start.vs_call_ctx` SUBST1_TAC >> simp[Abbr `cd`]) >>
      `LENGTH hit.vs_call_ctx.cc_calldata < dimword (:256) /\ 4 <= LENGTH hit.vs_call_ctx.cc_calldata` by
        (qpat_assum `hit.vs_call_ctx = start.vs_call_ctx` SUBST1_TAC >> conj_tac >> first_assum ACCEPT_TAC) >>
      `?z J tz. z.vs_returndata = [] /\
        !D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
          (hit,Gh,th) [] (Abort Revert_abort z,J,tz)` suffices_by
        (disch_then (qx_choosel_then [`z`,`J`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
         qexistsl_tac [`fn`,`z`,`J`,`tz`,`[]`] >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC >> NO_TAC) >> qx_gen_tac `D` >>
         irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> qexistsl_tac [`Gb`,`before`,`tb`] >>
         conj_tac >- first_assum (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC) >>
         irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> qexistsl_tac [`Gh`,`hit`,`th`] >>
         conj_tac >> first_assum (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC)) >>
      Cases_on `(~pay /\ hit.vs_call_ctx.cc_callvalue <> 0w) \/
        (4 < mc /\ LENGTH hit.vs_call_ctx.cc_calldata < mc)`
      >- (qpat_assum `selected_registration_resources unit.cu_context fn ARB 0 opened hit`
            (map_every assume_tac o CONJUNCTS o REWRITE_RULE [selected_registration_resources_def]) >>
          mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `m` |-> `mc`, `st` |-> `opened`,
                          `last` |-> `checked`, `s` |-> `hit`, `lo` |-> `0`, `PG` |-> `[]`,
                          `G` |-> `Gh`, `tn` |-> `th`]
                    (SPEC_ALL entryChecksRejectJointTheory.compile_entry_checks_reject_joint)) >>
          (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
            qpat_assum `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp hit /\ _`
              (fn h => simp[NoAsms, h]))) >>
          disch_then ACCEPT_TAC) >>
      (Q.SUBGOAL_THEN `mc <= LENGTH hit.vs_call_ctx.cc_calldata /\
         (pay \/ hit.vs_call_ctx.cc_callvalue = 0w)` (map_every assume_tac o CONJUNCTS) >-
        (reverse conj_tac
         >- (qpat_assum `~((~pay /\ _) \/ _)` mp_tac >> simp[NoAsms, DE_MORGAN_THM]) >>
         qpat_assum `~((~pay /\ _) \/ _)` mp_tac >>
         simp[NoAsms, DE_MORGAN_THM, GSYM AND_IMP_INTRO] >>
         disch_tac >>
         qpat_assum `4 <= LENGTH hit.vs_call_ctx.cc_calldata` mp_tac >> decide_tac)) >>
      `calldata_decode_args hit.vs_call_ctx.cc_calldata tvs 0 = NONE` by
        (qpat_assum `LENGTH cd < _ \/ calldata_decode_args cd tvs 0 = NONE` mp_tac >>
         qpat_assum `mc <= LENGTH hit.vs_call_ctx.cc_calldata` mp_tac >>
         qpat_assum `mc = 4 + SUM (MAP tv_abi_size tvs)` (fn mc_eq =>
           qpat_assum `hit.vs_call_ctx.cc_calldata = cd` (fn cc_eq =>
             simp[NoAsms, mc_eq, cc_eq, GSYM arithmeticTheory.NOT_LESS]))) >>
      (Q.SUBGOAL_THEN `mc <= 4 \/ mc <= LENGTH hit.vs_call_ctx.cc_calldata` assume_tac >-
        (disj2_tac >> first_assum ACCEPT_TAC)) >>
      mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `m` |-> `mc`, `sa` |-> `opened`,
                      `sb` |-> `checked`, `s` |-> `hit`, `lo` |-> `0`, `PG` |-> `[]`,
                      `site` |-> `ARB`, `G` |-> `Gh`, `tn` |-> `th`]
                (SPEC_ALL grouped_default_checks_pass_origin)) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choosel_then [`ready`,`Gr`,`trdy`] (map_every assume_tac o CONJUNCTS)) >>
      `ready.vs_call_ctx = hit.vs_call_ctx` by
        (qpat_assum `selected_registration_frame hit th ready trdy` mp_tac >>
         simp[NoAsms, selected_registration_frame_def]) >>
      `4 + SUM (MAP tv_abi_size tvs) <= LENGTH ready.vs_call_ctx.cc_calldata /\
       LENGTH ready.vs_call_ctx.cc_calldata < dimword (:256) /\
       calldata_decode_args ready.vs_call_ctx.cc_calldata tvs 0 = NONE` by
        (qpat_assum `ready.vs_call_ctx = hit.vs_call_ctx` SUBST1_TAC >>
         qpat_assum `mc = 4 + SUM (MAP tv_abi_size tvs)` (SUBST1_TAC o SYM) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `compile_register_positional_args ce (build_positional_args ce args) 4 checked = (cef,registered)` by
        (qpat_assum `pos = build_positional_args ce args` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      qpat_assum `selected_registration_resources unit.cu_context fn ARB 0 checked ready`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE [selected_registration_resources_def]) >>
      mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `env` |-> `tenv`, `site` |-> `ARB`,
                      `s` |-> `ready`, `G` |-> `Gr`, `tn` |-> `trdy`,
                      `sa` |-> `checked`, `sb` |-> `registered`]
                callRejectMemoryTheory.coherent_registration_reject_path) >>
      (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        rpt gen_tac >> strip_tac >>
        qpat_assum `!label bb. lookup_block label _ = SOME bb ==> _` (drule_then ACCEPT_TAC))) >>
      disch_then (qx_choosel_then [`z`,`J`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
      qexistsl_tac [`z`,`J`,`tz`] >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gr`,`ready`,`trdy`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      `~list$EXISTS is_default_decl (main_module mods) /\
        exported_fallback mods exps = NONE` by
        (qpat_assum `calldata_dispatch_mods mods exps cd = NONE` mp_tac >>
         qpat_assum `(if LENGTH cd < 4 then NONE else _) = NONE`
           (fn hit => simp[NoAsms, calldata_dispatch_mods_def, LET_THM, hit]) >>
         Cases_on `exported_fallback mods exps` >> simp[]) >>
      `fb = NONE` by drule_all_then ACCEPT_TAC linked_classified_fallback_absent >>
      `fall = NONE` by simp[Abbr `fall`, package_fallback_fn_unit_def,
                           set_fallback_package_target_def] >>
      `emit_inst REVERT [Lit 0w; Lit 0w] [] sn = ((),se)` by fs[] >>
      Cases_on `LENGTH cd < 4`
      >- (
          mp_tac (Q.INST [`ctx` |-> `unit.cu_context`,`s` |-> `start`,
             `st` |-> `sf`,`st'` |-> `sd`,`fallback` |-> `fl`,`lo` |-> `0`,
             `PG` |-> `[]`,`G` |-> `FEMPTY`,`tn` |-> `entry_taint`]
             (SPEC_ALL grouped_dispatch_short_prelude)) >>
          (impl_tac >-
            (`LENGTH start.vs_call_ctx.cc_calldata < 4` by simp[Abbr `cd`] >>
             conj_tac >- first_assum ACCEPT_TAC >>
             simp[] >> qpat_assum `!label bb. venomInst$lookup_block label _ = SOME bb ==> _`
               (qspec_then `fl` ACCEPT_TAC))) >>
          disch_then (qx_choosel_then [`q`,`r`,`t`,`G`,`tn`] strip_assume_tac) >>
          `allocas_from 0 t /\ allocas_below_fmp t` by
            (qpat_assum `vars_pc_only start t`
               (strip_assume_tac o SIMP_RULE (srw_ss())
                 [vars_pc_only_def, venom_state_component_equality]) >>
             fs[allocas_from_def, allocas_below_fmp_def]) >>
          `!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
             (t,G,tn) [] (Abort Revert_abort (revert_state (set_returndata [] t)),G,tn)` by
            (gen_tac >> irule emit_abort_origin_ptr >> simp[] >>
             qexistsl_tac [`REVERT`,`[Lit 0w; Lit 0w]`,`sn`,`se`] >>
             simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
          qexistsl_tac [`fn`,`revert_state (set_returndata [] t)`,`G`,`tn`,`[]`] >>
          simp[] >> conj_tac >- simp[revert_state_def, set_returndata_def] >>
          gen_tac >>
          qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) _ _`
            (qspecl_then [`D`,`EMPTY`] (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
          disch_then (qspecl_then [`t`,`G`,`tn`,`[]`,
            `Abort Revert_abort (revert_state (set_returndata [] t))`,`G`,`tn`] mp_tac) >>
          simp[] >> first_assum MATCH_ACCEPT_TAC) >>
      `4 <= LENGTH start.vs_call_ctx.cc_calldata` by simp[Abbr `cd`, NOT_LESS] >>
      `?target. venomInst$lookup_block fl fn.fn_blocks = SOME target` by
        (drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
         qpat_assum `fn_has_code sn se fn` (mp_tac o REWRITE_RULE [fn_has_code_def]) >>
         simp[] >> strip_tac >> qexists_tac `bb` >> first_assum ACCEPT_TAC) >>
      `EVERY (\group. case group of ExternalSingle (sel,lbl,tz) pkg =>
         calldata_method_id start.vs_call_ctx.cc_calldata <> n2w sel
       | ExternalDefaults common entries specs _ =>
         FIND (\(sel,_,_,_). calldata_method_id start.vs_call_ctx.cc_calldata = n2w sel)
           entries = NONE /\
         EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs) groups`
        suffices_by
          (disch_tac >>
           mp_tac (Q.INST [`ctx` |-> `unit.cu_context`,`s` |-> `start`,
              `sa` |-> `sf`,`sb` |-> `sd`,`fallback` |-> `fl`,`lo` |-> `0`,
              `site` |-> `ARB`,`PG` |-> `[]`,`G` |-> `FEMPTY`,`tn` |-> `entry_taint`]
              (SPEC_ALL grouped_dispatch_missed_fallback_origin)) >>
           (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
           disch_then (qx_choosel_then [`mid`,`q`,`r`,`t`,`G`,`tn`] strip_assume_tac) >>
           `!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
              (t,G,tn) [] (Abort Revert_abort (revert_state (set_returndata [] t)),G,tn)` by
             (gen_tac >> irule emit_abort_origin_ptr >> simp[] >>
              qexistsl_tac [`REVERT`,`[Lit 0w; Lit 0w]`,`sn`,`se`] >>
              simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def] >>
              strip_tac >> first_x_assum drule >> simp[]) >>
           qexistsl_tac [`fn`,`revert_state (set_returndata [] t)`,`G`,`tn`,`[]`] >>
           simp[] >> conj_tac >- simp[revert_state_def, set_returndata_def] >>
           gen_tac >>
           qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) _ _`
             (qspecl_then [`D`,`EMPTY`] (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
           disch_then (qspecl_then [`t`,`G`,`tn`,`[]`,
             `Abort Revert_abort (revert_state (set_returndata [] t))`,`G`,`tn`] mp_tac) >>
           simp[] >> first_assum MATCH_ACCEPT_TAC) >>
      `4 <= LENGTH cd` by simp[Abbr `cd`] >>
      `FIND (\(nm,ts). abi_method_id (type_env_all_modules mods) nm ts = cd_selector cd)
         (abi_deployed_signatures mods exps) = NONE` by fs[] >>
      `~MEM (cd_selector cd) (MAP FST (grouped_selectors groups))` by
        (simp[Abbr `groups`] >> strip_tac >>
         qpat_assum `!ks id. MEM id _ ==> _` drule >>
         disch_then (qx_choosel_then [`hit_key`,`nm`,`ts`,`pf`,`nk`] strip_assume_tac) >>
         qpat_x_assum `hit_key = _` SUBST_ALL_TAC >>
         qpat_assum `!src mut nr rr name args ds ret code pref k. MEM _ exts /\ _ ==> _`
           drule_all >> strip_tac >>
         qpat_assum `FIND _ (abi_deployed_signatures mods exps) = NONE`
           (mp_tac o SIMP_RULE (srw_ss())
             [mem2varBlockSimHelpersTheory.FIND_NONE_EVERY, EVERY_MEM,
              combinTheory.o_DEF, FORALL_PROD]) >>
         disch_then (qspecl_then [`nm`,`ts`] mp_tac) >> simp[]) >>
      `EVERY (\group. case group of ExternalSingle (sel,lbl,tz) pkg =>
         calldata_method_id start.vs_call_ctx.cc_calldata <> n2w sel
       | ExternalDefaults common entries _ _ =>
         FIND (\(sel,_,_,_). calldata_method_id start.vs_call_ctx.cc_calldata = n2w sel)
           entries = NONE) groups` by
        (irule groupedEntryPackageTheory.grouped_selector_misses >>
         `w2n (calldata_method_id start.vs_call_ctx.cc_calldata) = cd_selector cd` by
           (simp[GSYM calldataSelectorPropsTheory.cd_selector_method_id, Abbr `cd`]) >>
         simp[Abbr `groups`]) >>
      simp[EVERY_MEM] >> qx_gen_tac `g` >> strip_tac >>
      qpat_assum `EVERY (\g. case g of ExternalSingle _ _ => _ | ExternalDefaults _ _ _ _ => _) groups`
        (mp_tac o Q.SPEC `g` o REWRITE_RULE [EVERY_MEM]) >>
      Cases_on `g` >> simp[] >>
      qpat_assum `!common entries specs off. MEM (ExternalDefaults _ _ _ _) groups ==> _`
        drule >> simp[EVERY_MEM]
QED

Finalise lower_vyper_runtime_unit_reverts_mods
