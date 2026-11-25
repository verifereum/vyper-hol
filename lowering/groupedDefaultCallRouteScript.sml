(* Selected default entry: value check, initialization, and the common-body cut. *)
Theory groupedDefaultCallRoute
Ancestors
  groupedRuntimeBodyCode groupedEntryPackage groupedEntryResources groupedSelectedDefault
  entryCreateGroupedLayout
  groupedDefaultValueRejection groupedEntryExit groupedDefaultPassingExecution groupedDefaultBoundEntry
  groupedDefaultGuardedStart groupedDefaultCutTransport groupedEntryCut entryRejectCode
  fragGasPathPtr fragGasPath fragFuelRuntimeBody fragFuelRuntimePackage fragFuelCtx fragFuel fragFuelUnit
  loweringShapeDefs entryCodeOwnership emitHelperProps exprLoweringProps
  groupedDefaultArguments groupedDefaultSource groupedDefaultState groupedDefaultSyntax
  groupedDefaultHorizon groupedEntryCounters groupedInternalLabels groupedRegistrationCounters
  groupedEntryAllocation defaultEntrySourcePreparation bodyFullShadowBodyInvLowering bodyPtrDefs
  allocaHistory abiAllocationHistory entryPtrSeamRegister vyperCompiler venomExecProofs
  decoderOriginAllocationFrame bodyFullPathHistory vyperStorageTrace vyperTypeContractStaticMaps
  loweringShapeProps
  registrationRejectMetadata defaultRegistrationState defaultConcreteRegistrationDefs
  externalBodyFrame bodyInvSplit bodyInvMetadataProps bodyInvExecutionProps entryStateRel
  gasShadowUnit gasShadowRuntimeBodies gasShadowRunLowering gasShadowModuleDefs gasShadow
  moduleLowering compileVyper compileEnv gasSummary ptrDiscipline vyperLoweringCorrect
  e2eDefs loweringStateRelDefs sourceUnitExecution runtimeEntryEndpoint
  vyperABI vyperABIEntries vyperCalldata vyperTypeABI vyperTypeContractGetter
  vyperReadOnlySyntax vyperTypeContractContext vyperTypeContract entryDispatchProps
  sourceValueRejection abiDecoderCoherence ctorRegisterArgs selectedAcceptedSingleton selectedAcceptedDecoder
  vyperInterpreter vyperState vyperCall vyperContext vyperStorageFootprint constSubstCorrect
  selectedAcceptedFold fragGasOriginPtr fragGasOriginPtrLoop fragExec
  dispatchedDecodeDomain dispatchedDecodeCast vyperTyping constSubst
  venomInst venomState words arithmetic list rich_list pair finite_map

val shadow_group = ``\group. case group of
  ExternalSingle selector package =>
    ExternalSingle selector (gas_shadow_external_package package)
| ExternalDefaults common entries specs off =>
    ExternalDefaults (common with <| ec_env := gas_shadow_env T common.ec_env;
      ec_body := MAP gas_shadow_stmt common.ec_body |>)
      entries (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off``;

val shadow_job = ``\job. case job of
  ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
| ExternalCommonJob common kwvars => ExternalCommonJob
    (common with <| ec_env := gas_shadow_env T common.ec_env;
      ec_body := MAP gas_shadow_stmt common.ec_body |>)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars)``;

val start = ``vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>``;
val ctx = ``unit.cu_context``;
val explicit = ``gas_explicit_sites unit.cu_context shadow_unit.cu_context``;
val empty_h = ``([],[]):(bool # bytes32 # type_value) list # num list``;
val cx = ``initial_evaluation_context am.sources am.layouts tx NONE``;
val ce = ``common.ec_env``;
val c0 = ``^ce with ce_vars := FEMPTY``;
val src = ``initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>``;
val cd = ``vs.vs_call_ctx.cc_calldata``;
val pos = ``LENGTH (args:(string # type) list) - LENGTH (dflts:expr list)``;
val rr = ``lookup_raw_return_or_F (NONE:num option) tx.function_name External tops``;
val ds = ``subst_consts_exprs (module_consts_env tops []) dflts``;
val ss = ``subst_consts_stmts (module_consts_env tops []) fbody``;

fun package defaults = ``set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,^rr,tx.function_name,args,^defaults,ret,^ss))``;
val no_defaults_pkg = package ``[]:expr list``;
val defaults_pkg = package ds;

(* The callbacks consume exactly the premises at the selected value check
   and the passing initializer.  Keep their long interfaces single-sourced
   in the two producers rather than repeating the conjunctions here. *)
val route_exit = ``route_exit:bool``;
val selected_value_cases = Q.INST
  [`shadow_ctx` |-> `shadow_unit.cu_context`, `reject_result` |-> `^route_exit`]
  (SPEC_ALL grouped_selected_default_value_rejection_cases);
val (reject_handler, _) = dest_imp (concl selected_value_cases);
val (pass_inputs, pass_result) = dest_imp (concl (Q.INST
  [`rp` |-> `rpolicy`, `raw` |-> `dflts`]
  (SPEC_ALL grouped_default_passing_execution)));
val (initializer_exit, initializer_done) = dest_disj pass_result;
val route_parameters = ["tops","rpolicy","unit","shadow_unit","am","tx","vs",
                        "mut","nr","args","dflts","ret","fbody","route_exit"];
fun route_handler statement =
  list_mk_forall
    (filter (fn v => not (mem (fst (dest_var v)) route_parameters))
      (free_vars statement), statement);
val init_handler = route_handler
  ``^pass_inputs ==> ^route_exit \/ ^initializer_done``;
val init_layout = ``cs_extends si sb /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sb)) /\
  ?term. emit_inst JMP [Label common.ec_common_label] [] sb = ((),term) /\
    fn_has_code sb term fn``;
val init_binders = fst (strip_forall init_handler);
val init_handler_with_layout = list_mk_forall (init_binders,
  ``^pass_inputs ==> ^init_layout ==> ^route_exit \/ ^initializer_done``);

(* Specialize the callback's bound variables using the same named aliases
   as the original initializer application; the entry cursor s stays free. *)
val init_arguments =
  let
    val aliases = [("ds",`^ds`),("ss",`^ss`),("rr",`^rr`),("s",`v`),
      ("es",`ev`),("G",`Gv`),("tn",`tnv`),("a",`astart`),("b",`aend`),
      ("sha",`shsi`),("shb",`shsb`),("site",`ARB:instruction`)];
    fun argument v =
      case List.find (fn (name,_) => name = fst (dest_var v)) aliases of
        SOME (_, actual) => actual
      | NONE => [ANTIQUOTE v];
  in map argument (fst (strip_forall init_handler_with_layout)) end;

val route_inputs = ``
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
  (ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==> dalloca_fmp_headroom inst s) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\ dflts <> [] /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts =
    cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
      SOME (tx.function_name,tys) /\
  OPT_MMAP (evaluate_type (type_env tops)) tys = SOME provided /\
  4 + SUM (MAP tv_abi_size provided) <= LENGTH vs.vs_call_ctx.cc_calldata /\
  calldata_decode_args vs.vs_call_ctx.cc_calldata provided 0 = SOME tx.args``;
val selected_endpoint = ``
  ?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args dflts ret
    (subst_consts_stmts (module_consts_env tops []) fbody)``;

Theorem grouped_default_route_elim_with_init_layout:
  ^route_inputs ==> ^reject_handler ==> ^init_handler_with_layout ==>
  ^selected_endpoint \/ ^route_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  disch_then (mk_asm "on_value_reject") >>
  disch_then (mk_asm "on_initializer") >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = functions` >>
  PairCases_on `functions` >>
  rename1 `classify_functions tops = (externals,internals,fallback,constructor)` >>
  fs[] >>
  drule_all lower_grouped_runtime_pair >>
  disch_then (qx_choosel_then [`groups`,`ips`,`fall`,`shunit`,`fn`,`bb`]
    (map_every assume_tac o CONJUNCTS)) >>
  `shunit = shadow_unit` by fs[] >> gvs[] >>
  drule_all grouped_shadow_entry_dispatch_with_layout >>
  disch_then (qx_choosel_then
    [`shunit`,`shfn`,`sf`,`fall_lbl`,`jobs`,`sd`,`shd`,`sx`,`shx`,`sn`,`shn`,`se`,`she`]
    (map_every assume_tac o CONJUNCTS)) >>
  `shunit = shadow_unit` by fs[] >> gvs[] >>
  suspend "selector"
QED

Resume grouped_default_route_elim_with_init_layout[selector]:
  `4 <= LENGTH ^cd` by decide_tac >>
  qabbrev_tac `groups = MAP (package_external_group tops rpolicy.rpol_target T
    (K global_nonreentrant_slot)) externals` >>
  `groups = MAP (package_external_group tops rpolicy.rpol_target T
    (K global_nonreentrant_slot)) externals` by simp[Abbr `groups`] >>
  drule_all grouped_selected_default_entry_shape >>
  disch_then (qspecl_then [`T`,`rpolicy.rpol_target`,`K global_nonreentrant_slot`]
    (qx_choosel_then [`pre`,`post`,`prefix`,`k`,`common`,`entries`,`specs`,`off`]
      (map_every assume_tac o CONJUNCTS))) >>
  `groups = pre ++ ExternalDefaults common entries specs off::post` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >>
     qpat_assum `classify_functions tops = _` (fn eq =>
       qpat_assum `MAP _ (FST (classify_functions tops)) = _`
         (ACCEPT_TAC o REWRITE_RULE [eq,FST]))) >>
  `EVERY (\group. case group of ExternalSingle _ _ => T
    | ExternalDefaults c ens sp o' =>
      EVERY (\(_,ty,_). type_memory_bytes c.ec_env ty < dimword (:256)) sp) groups` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >>
     irule (INST_TYPE [alpha |-> ``:160 word``] checked_grouped_package_keyword_widths) >>
     conj_tac >- (qexistsl_tac [`rpolicy`,`unit`] >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexistsl_tac [`tx.target`,`art`,`am.layouts`] >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`constructor`,`fallback`,`internals`] >> first_assum ACCEPT_TAC) >>
  qpat_assum `EVERY _ groups` (fn th =>
    qpat_assum `groups = pre ++ _` (fn eq =>
      strip_assume_tac (SIMP_RULE (srw_ss()) [eq,EVERY_APPEND] th))) >>
  `EVERY (\group. case group of
      ExternalSingle (sel,_,_) _ => calldata_method_id ^cd <> n2w sel
    | ExternalDefaults c ens sp _ =>
        FIND (\(sel,_,_,_). calldata_method_id ^cd = n2w sel) ens = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes c.ec_env ty < dimword (:256)) sp) pre` by
    (PURE_REWRITE_TAC [EVERY_MEM] >> qx_gen_tac `group` >> strip_tac >>
     qpat_x_assum `EVERY _ pre`
       (mp_tac o Q.SPEC `group` o REWRITE_RULE [EVERY_MEM]) >>
     qpat_assum `EVERY _ pre`
       (mp_tac o Q.SPEC `group` o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `group` >> simp[pairTheory.ELIM_UNCURRY]) >>
  `LENGTH tx.args = LENGTH prefix` by
    (drule calldata_decode_args_length >>
     qpat_assum `OPT_MMAP _ _ = SOME provided` (mp_tac o MATCH_MP OPT_MMAP_LENGTH) >> simp[]) >>
  qpat_assum `tys = MAP SND prefix` (fn th =>
    qpat_assum `OPT_MMAP _ tys = SOME provided` (assume_tac o REWRITE_RULE [th])) >>
  qpat_assum `gas_shadow_unit unit shadow_unit`
    (strip_assume_tac o REWRITE_RULE [gas_shadow_unit_def]) >>
  `MEM fn unit.cu_context.ctx_functions /\ MEM shfn shadow_unit.cu_context.ctx_functions` by
    (conj_tac >> irule venomInstTheory.lookup_function_MEM >> goal_assum (drule_at Any)) >>
  `(ctx_has_dalloca ^ctx ==> unit_alloca_budget ^ctx <= w2n vs.vs_initial_fmp)` by
    (strip_tac >> qpat_assum `ctx_has_dalloca _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `(?ev. send_call_value mut ^cx ^src = (INL (),ev)) \/
   (?e ev. send_call_value mut ^cx ^src = (INR e,ev))` by
    (Cases_on `send_call_value mut ^cx ^src` >>
     rename1 `send_call_value _ _ _ = (value_result,ev)` >>
     Cases_on `value_result` >> simp_tac (srw_ss()) [])
  >- (rename1 `send_call_value _ _ _ = (INL (),ev)` >> suspend "accept")
  >> suspend "reject"
QED

Resume grouped_default_route_elim_with_init_layout[reject]:
  disj2_tac >>
  asm "on_value_reject" (drule_all o MATCH_MP selected_value_cases) >> simp[]
QED

Resume grouped_default_route_elim_with_init_layout[accept]:
  `send_call_value mut ^cx ^src = (INL (),ev)` by
    (qpat_assum `send_call_value _ _ _ = (INL _,_)` mp_tac >> simp_tac (srw_ss()) []) >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC) `common.ec_payable \/ vs.vs_call_ctx.cc_callvalue = 0w`
   >- (drule send_call_value_success_condition >>
     qpat_assum `initial_venom_state_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [initial_venom_state_rel_def,venom_env_rel_def,call_ctx_rel_def]) >>
     simp_tac (srw_ss()) [initial_evaluation_context_def] >> asm_rewrite_tac[] >>
     strip_tac >> simp[])) >>
  `MEM (tx.function_name,tys) (abi_external_signatures tops)` by
    (irule venomInstTheory.FIND_MEM >> goal_assum (drule_at Any)) >>
  drule_all grouped_source_signature >>
  disch_then (qx_choosel_then [`before`,`after`,`other_prefix`,`other_k`]
    (map_every assume_tac o CONJUNCTS)) >>
  `MEM (mut,nr,^rr,tx.function_name,args,^ds,ret,^ss) (FST (classify_functions tops))` by
    (qpat_assum `FST (classify_functions tops) = _` SUBST1_TAC >> simp_tac (srw_ss()) [MEM_APPEND]) >>
  `MEM (FunctionDecl External mut nr ^rr tx.function_name args dflts ret fbody) tops` by
    (drule entryDispatchPropsTheory.lookup_function_external_raw_cases >> strip_tac
     >- simp[lookup_raw_return_or_F_def] >>
     drule vyperReadOnlySyntaxTheory.external_getter_defaults >> simp[]) >>
  drule_all grouped_checked_default_syntax >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "package"
QED

Resume grouped_default_route_elim_with_init_layout[package]:
  Cases_on `^no_defaults_pkg` >>
  rename1 `set_external_package_target _ _ = (_,rest)` >> PairCases_on `rest` >>
  rename1 `set_external_package_target _ _ = (lbl,ce0,pa,fullcd,pay,guarded,key,ut,view,ss',rt)` >>
  `guarded = nr /\ ss' = ^ss` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [package_external_fn_def,set_external_package_target_def,LET_THM] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> asm_rewrite_tac[]) >>
  qpat_x_assum `guarded = nr` SUBST_ALL_TAC >> qpat_x_assum `ss' = _` SUBST_ALL_TAC >>
  drule_all registration_reject_classified_defaults_metadata >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `tvs` (map_every assume_tac o CONJUNCTS)))) >>
  `?mc. ^defaults_pkg = (lbl,ce0,pa,mc,pay,nr,key,ut,view,^ss,rt)` by
    (qpat_assum `^no_defaults_pkg = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [package_external_fn_def,set_external_package_target_def,LET_THM,subst_consts_exprs_map] >>
     strip_tac >> qpat_x_assum `(mut = View) = view` (SUBST_ALL_TAC o SYM) >>
     asm_rewrite_tac[]) >>
  drule_all grouped_package_common_environment >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `common.ec_env = ce0` (SUBST_ALL_TAC o SYM) >>
  suspend "decoder"
QED

Resume grouped_default_route_elim_with_init_layout[decoder]:
  `LENGTH tvs = LENGTH args` by
    (qpat_assum `OPT_MMAP _ _ = SOME tvs` (mp_tac o MATCH_MP OPT_MMAP_LENGTH) >> simp_tac (srw_ss()) []) >>
  `!i. i < LENGTH args ==>
     abi_decoder_coherent ^ce (type_env tops) (^ce).ce_struct_fields (SND (EL i args)) (EL i tvs) /\
     type_memory_size (EL i tvs) < dimword (:256)` by
    (rpt strip_tac >>
     qpat_assum `LIST_REL _ args (ZIP _)`
       (qspec_then `i` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     Cases_on `EL i args` >> simp[EL_ZIP,EL_MAP]) >>
  `LIST_REL (\arg tv. abi_decoder_coherent ^ce (type_env tops) (^ce).ce_struct_fields (SND arg) tv)
    args tvs` by
    (pure_rewrite_tac[LIST_REL_EL_EQN] >> conj_tac >- asm_rewrite_tac[] >>
     CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt strip_tac >>
     qpat_assum `!i. i < LENGTH args ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  drule_all grouped_default_decode_split >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `min_calldata_size ^ce prefix 0 = 4 + SUM (MAP tv_abi_size provided)` by
    (qpat_assum `MEM (prefix,k) _` (strip_assume_tac o REWRITE_RULE [abi_entries_member]) >>
     qpat_assum `prefix = TAKE _ _` SUBST1_TAC >>
     qpat_assum `provided = _` (SUBST1_TAC o REWRITE_RULE [GSYM TAKE_SUM]) >>
     irule grouped_argument_min_calldata_size >> goal_assum (drule_at Any)) >>
  `min_calldata_size ^ce prefix 0 <= LENGTH ^cd` by decide_tac >>
  `off = 4 + SUM (MAP tv_abi_size (TAKE ^pos tvs))` by
    (qpat_assum `off = _` SUBST1_TAC >> irule grouped_argument_min_calldata_size >> goal_assum (drule_at Any)) >>
  suspend "start"
QED

Resume grouped_default_route_elim_with_init_layout[start]:
  qabbrev_tac `s = ^start` >>
  `s = ^start` by simp[Abbr `s`] >>
  `s.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `s = _` SUBST1_TAC >> simp_tac (srw_ss()) []) >>
  `4 <= LENGTH s.vs_call_ctx.cc_calldata /\ min_calldata_size ^ce prefix 0 <= LENGTH s.vs_call_ctx.cc_calldata` by
    (qpat_assum `s.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all (Q.INST [`st` |-> `sf`] (SPEC_ALL grouped_dispatch_initial_resources)) >>
  disch_then (qspec_then `ARB:instruction` (map_every assume_tac o CONJUNCTS)) >>
  `EVERY group_entry_labels_ok (MAP ^shadow_group groups)` by
    (pure_rewrite_tac [EVERY_MAP,EVERY_MEM,combinTheory.o_DEF] >>
     qx_gen_tac `group` >> strip_tac >>
     qpat_assum `EVERY group_entry_labels_ok groups`
       (drule_then mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `group`
     >- (rename1 `ExternalSingle selector pkg` >> PairCases_on `selector` >>
         PairCases_on `pkg` >> simp_tac (srw_ss()) [group_entry_labels_ok_def,gas_shadow_external_package_def]) >>
     simp_tac (srw_ss()) [group_entry_labels_ok_def]) >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
      `min_calldata_size ^ce prefix 0 <= 4 \/
       min_calldata_size ^ce prefix 0 <= LENGTH s.vs_call_ctx.cc_calldata`
   >- (disj2_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `s.vs_call_ctx = vs.vs_call_ctx` (fn eq =>
    qpat_assum `EVERY _ pre` (assume_tac o REWRITE_RULE [SYM eq]) >>
    qpat_assum `FIND _ entries = _` (assume_tac o REWRITE_RULE [SYM eq]) >>
    qpat_assum `common.ec_payable \/ _` (assume_tac o REWRITE_RULE [SYM eq])) >>
  drule_all (Q.INST [`G` |-> `FEMPTY`, `tn` |-> `entry_taint`, `PG` |-> `[]`]
    (SPEC_ALL grouped_selected_default_initializer_start)) >>
  disch_then (qx_choosel_then
    [`vars`,`astart`,`aend`,`checks`,`si`,`sb`,`term`,`dispatch_end`,`shsi`,`shsb`,
     `hit`,`Gh`,`thit`,`v`,`Gv`,`tnv`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "source_state"
QED

Resume grouped_default_route_elim_with_init_layout[source_state]:
  drule_all (REWRITE_RULE [] (Q.INST [`cx` |-> `^cx`]
    (SPEC_ALL grouped_default_empty_source_frame))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (REWRITE_RULE [] (Q.INST [`cx` |-> `^cx`] (SPEC_ALL grouped_default_empty_expr_sim))) >>
  disch_then assume_tac >>
  `(^c0) with ce_vars := (^ce).ce_vars = ^ce` by
    simp_tac (srw_ss()) [compile_env_component_equality] >>
  drule_all (Q.INST [`cenv` |-> `^c0`] (SPEC_ALL external_package_body_inv)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_body_registration_layout >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule source_typing_ok_vtype_keys_distinct >> disch_then assume_tac >>
  drule_all runtime_shadow_body_inv >> disch_then assume_tac >>
  suspend "passing_resources"
QED

Resume grouped_default_route_elim_with_init_layout[passing_resources]:
  drule (cj 1 registration_runtime_acceptance) >> disch_then assume_tac >>
  drule (cj 1 lowering_context_ok_static_integrity) >> disch_then assume_tac >>
  `ALL_DISTINCT (fn_labels fn)` by
    (drule (cj 1 lowering_context_ok_bridge) >> simp_tac bool_ss [EVERY_MEM] >>
     disch_then (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `!l b. lookup_block l fn.fn_blocks = SOME b ==> _`
       (drule_then ACCEPT_TAC)) >>
  `!b. MEM b fn.fn_blocks ==> phi_prefix_length b.bb_instructions = 0` by
    (rpt strip_tac >> qpat_assum `!l bb. lookup_block l fn.fn_blocks = SOME bb ==> _` irule >>
     qexists_tac `b.bb_label` >> irule venomExecProofsTheory.MEM_lookup_block >>
     asm_simp_tac (srw_ss()) [GSYM fn_labels_def]) >>
  qpat_assum `^defaults_pkg = _`
    (map_every assume_tac o CONJUNCTS o MATCH_MP targeted_external_package_layout) >>
  `selected_registration_frame vs entry_taint v tnv` by
    (qpat_assum `selected_registration_frame s entry_taint v tnv` mp_tac >>
     qpat_assum `s = _` SUBST1_TAC >> simp_tac (srw_ss()) [selected_registration_frame_def]) >>
  qpat_assum `selected_registration_frame vs entry_taint v tnv`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [selected_registration_frame_def,entry_taint_def]) >>
  `calldata_decode_args v.vs_call_ctx.cc_calldata provided 0 = SOME tx.args` by
    (qpat_assum `v.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  suspend "alloca"
QED

Resume grouped_default_route_elim_with_init_layout[alloca]:
  `s.vs_inst_idx = 0` by
    (qpat_assum `s = _` SUBST1_TAC >> simp_tac (srw_ss()) []) >>
  `alloca_history fn s` by (irule alloca_history_empty >> asm_rewrite_tac[]) >>
  `abi_alloca_history (fn_insts fn) s` by (irule abi_alloca_history_empty >> first_assum ACCEPT_TAC) >>
  qpat_assum `selected_registration_resources _ fn _ 0 sf s`
    (assume_tac o cj 3 o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_assum `!D e. gas_origin_ptr_path _ (s,FEMPTY,entry_taint) [] (OK v,Gv,tnv)`
    (qspecl_then [`cx_dead ([],[]) ^cx`,`{}`] assume_tac) >>
  drule_all body_full_path_alloca_history >> disch_then assume_tac >>
  drule_all grouped_entry_path_abi_history >> disch_then assume_tac >>
  drule_all decoder_origin_path_allocation_frame >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by
    (qpat_assum `s = _` SUBST1_TAC >> simp_tac (srw_ss()) []) >>
  qpat_assum `initial_venom_state_rel _ _ _ vs`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [initial_venom_state_rel_def]) >>
  `v.vs_fmp = v.vs_initial_fmp` by (asm_rewrite_tac[]) >>
  `(ctx_has_dalloca ^ctx ==> unit_alloca_budget ^ctx <= w2n v.vs_initial_fmp /\
    w2n v.vs_initial_fmp < 2 ** 254)` by
    (qpat_assum `v.vs_initial_fmp = _` SUBST1_TAC >>
     qpat_assum `s.vs_initial_fmp = _` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca _ ==> unit_alloca_budget _ <= w2n vs.vs_initial_fmp /\ _`
       mp_tac >> simp_tac (srw_ss()) []) >>
  `default_registration_resources ^ctx fn ARB 0 si v (tnv with t_mem := {})` by
    (irule grouped_default_registration_resources >> asm_simp_tac (srw_ss()) []) >>
  suspend "guarded_state"
QED

Resume grouped_default_route_elim_with_init_layout[guarded_state]:
  `(^cx).txn = tx` by simp_tac (srw_ss()) [initial_evaluation_context_def] >>
  `(^c0).ce_vars = FEMPTY /\ ~(^c0).ce_is_ctor /\ (^c0).ce_imm_alloca = NONE /\
   (^c0).ce_return_buf = NONE /\ (^ce).ce_return_pc = NONE` by
    (qpat_assum `(^c0).ce_return_pc = NONE` mp_tac >>
     simp_tac (srw_ss()) [] >> asm_rewrite_tac[]) >>
  `!H. dead_lo_ok H (cx_dead H ^cx) 0 ^c0 ^cx` by
    (qpat_assum `~(^c0).ce_is_ctor` mp_tac >> simp_tac (srw_ss()) [dead_lo_ok_def,dead_sub_def]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
      valid_horizon ^cx (initial_state am []) H ev.storage_trace ==>
      stmt_state_rel H ^ctx fn ^c0 ^cx ev v /\
      storage_well_formed_on ^cx ev (FST H) /\
      ghost_inv_at (cx_dead H ^cx) 0 NONE ^c0 ^cx ev Gv tnv v` by
    (rpt gen_tac >> strip_tac >>
     drule_at (Pat `valid_horizon _ _ H ev.storage_trace`)
       (Q.INST [`site` |-> `ARB:instruction`] (SPEC_ALL grouped_default_guarded_start)) >>
     disch_then irule >> asm_rewrite_tac[] >> conj_tac
     >- (qexistsl_tac [`mut`,`tops`,`tx`,`vs`] >> asm_rewrite_tac[]) >>
     qexists_tac `si` >> asm_rewrite_tac[]) >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` by
    (qpat_assum `source_deployment_rel _ _ _` (map_every assume_tac o CONJUNCTS o REWRITE_RULE [source_deployment_rel_def]) >>
     first_assum ACCEPT_TAC) >>
  `get_tenv ^cx = type_env tops /\ (artifact_env art [(NONE,tops)] NONE).type_defs = get_tenv ^cx` by
    (simp_tac (srw_ss()) [get_tenv_def,initial_evaluation_context_def,artifact_env_def] >>
     asm_simp_tac (srw_ss()) [type_env_all_modules_def,type_env_def,FUNION_FEMPTY_2]) >>
  `ev.storage_trace = (initial_state am []).storage_trace /\
    storage_trace_domain ^cx (initial_state am []) ev.storage_trace` by
    (qpat_assum `ev.storage_trace = []` SUBST1_TAC >>
     simp_tac (srw_ss()) [initial_state_def,storage_trace_domain_def,storage_trace_horizon_def,
       storage_trace_regions_def,storage_trace_locks_def] >>
     irule grouped_default_empty_regions_horizon >>
     simp_tac (srw_ss()) [storage_trace_regions_def,storage_trace_locks_def]) >>
  suspend "run_init"
QED

Resume grouped_default_route_elim_with_init_layout[run_init]:
  `LENGTH ^ds = LENGTH dflts` by simp[subst_consts_exprs_map] >>
  `MEM (prefix,k) (abi_entries args ^ds)` by
    (qpat_assum `MEM (prefix,k) (abi_entries args dflts)` mp_tac >>
     pure_rewrite_tac[abi_entries_member] >> asm_rewrite_tac[]) >>
  `!D e. gas_origin_ptr_path (D,0,e,^ctx,fn,[]) (^start,FEMPTY,entry_taint) [] (OK v,Gv,tnv)` by
    (qpat_assum `s = _` (fn eq => simp_tac bool_ss [GSYM eq]) >> first_assum ACCEPT_TAC) >>
  asm "on_initializer" (qspecl_then init_arguments mp_tac) >>
  impl_tac >- suspend "init_pre" >>
  impl_tac >- (drule_all_then strip_assume_tac selected_initializer_layout_at >>
    asm_rewrite_tac[] >> qexists_tac `term` >> asm_rewrite_tac[]) >>
  disch_then (DISJ_CASES_THEN2
    (fn th => disj2_tac >> ACCEPT_TAC th)
    (qx_choosel_then [`slots`,`last`,`t`,`J`,`tz`,`marks`,`values`,`ee`,`u`,`Gu`,`tu`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "normal"
QED

Resume grouped_default_route_elim_with_init_layout[init_pre]:
  qpat_assum `MEM (mut,nr,^rr,tx.function_name,args,^ds,ret,^ss)
    (FST (classify_functions tops))` (fn mem_th =>
    qpat_assum `classify_functions tops = _`
      (assume_tac o (fn eq => PURE_REWRITE_RULE [eq,FST] mem_th))) >>
  pure_rewrite_tac[] >>
  qpat_assum `LENGTH ^ds = LENGTH dflts` (pure_rewrite_tac o single) >>
  qpat_assum `off = 4 + SUM _` (pure_rewrite_tac o single o SYM) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qpat_assum `fullcd = 4 + SUM _` (pure_rewrite_tac o single o SYM) >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `!name op ty e. MEM (name,op,ty,e) vars ==> _`
    mp_tac >> simp[AC CONJ_ASSOC CONJ_COMM]
QED

Resume grouped_default_route_elim_with_init_layout[normal]:
  disj1_tac >>
  qpat_assum `MEM (ExternalCommonJob common vars) jobs`
    (qx_choosel_then [`jpre`,`jpost`] assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  qpat_assum `jobs = jpre ++ _` (fn eq =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  drule_all grouped_common_job_guarded_code >>
  disch_then (qx_choosel_then [`ce`,`job_start`,`entry`,`sa`,`done`,`shentry`,`shsa`,`shdone`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `entry.cs_current_bb = common.ec_common_label` (fn eq =>
    qpat_assum `emit_inst JMP _ _ sb = _` (assume_tac o PURE_REWRITE_RULE [GSYM eq]) >>
    qpat_assum `new_block common.ec_common_label job_start = _`
      (assume_tac o PURE_ONCE_REWRITE_RULE [GSYM eq])) >>
  drule_all grouped_cut_counters >> disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "retained"
QED

Resume grouped_default_route_elim_with_init_layout[retained]:
  `cs_extends done sx` by
    (drule_all compile_external_common_job_interval >>
     qpat_assum `compile_external_jobs jpre sd = _` (fn pre =>
       qpat_assum `new_block common.ec_common_label job_start = _` (fn opened =>
         qpat_assum `compile_register_positional_args _ _ 4 entry = _` (fn reg =>
           qpat_assum `compile_guarded_body _ _ _ _ _ _ _ sa = _` (fn body =>
             simp_tac (srw_ss()) [pre,opened,reg,body])))) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `cs_extends checks sb /\ cs_extends sb sd /\ cs_extends term entry /\ cs_extends sb entry` by
    (conj_tac >-
      (irule cs_extends_trans >> qexists_tac `si` >> conj_tac >>
       first_assum (ACCEPT_TAC o cj 1 o PURE_REWRITE_RULE [ci_mono_def])) >>
     rpt conj_tac >>
     first_assum (ACCEPT_TAC o cj 1 o PURE_REWRITE_RULE [ci_mono_def])) >>
  `cs_extends done se /\ cs_extends sb done` by
    (conj_tac >> irule cs_extends_trans
     >- (qexists_tac `sx` >> conj_tac >> first_assum ACCEPT_TAC) >>
     qexists_tac `entry` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code checks sb fn` by
    (irule fn_has_code_retained_interval >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `se` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule cs_extends_trans >> qexists_tac `done` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code entry done fn` by
    (irule fn_has_code_retained_interval >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `se` >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac selected_grouped_body_layout_at >>
  suspend "cut_path"
QED

Resume grouped_default_route_elim_with_init_layout[cut_path]:
  `ee.storage_trace = []` by
    (qpat_assum `(ee with gas_obs := []) = _`
       (mp_tac o AP_TERM ``evaluation_state_storage_trace``) >>
     qpat_assum `ev.storage_trace = []` (fn th => simp_tac (srw_ss()) [th])) >>
  `valid_horizon ^cx (initial_state am []) ^empty_h ee.storage_trace` by
    (qpat_assum `ee.storage_trace = []` (fn th =>
       simp_tac (srw_ss()) [th,grouped_default_empty_regions_horizon,storage_trace_regions_def,storage_trace_locks_def])) >>
  `!D e. gas_origin_ptr_path (D,0,e,^ctx,fn,[]) (hit,Gh,thit) [] (OK t,J,tz)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >> simp_tac bool_ss [APPEND] >>
     qexistsl_tac [`Gv`,`v`,`tnv`] >> conj_tac >>
     first_assum (fn th => ACCEPT_TAC (Q.SPECL [`D`,`e`] th))) >>
  `!H. valid_horizon ^cx (initial_state am []) H ee.storage_trace ==>
       gas_origin_ptr_path (cx_dead H ^cx,0,^explicit,^ctx,fn,[])
         (hit,Gh,thit) marks (OK u,Gu,tu)` by
    (rpt gen_tac >> strip_tac >>
     irule (SIMP_RULE bool_ss [APPEND] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_origin_ptr_path_append))) >>
     qexistsl_tac [`J`,`t`,`(OK t,J,tz)`,`tz`] >> simp_tac bool_ss [] >> conj_tac
     >- simp[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (t,J,tz) marks _ /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  `!H. valid_horizon ^cx (initial_state am []) H ee.storage_trace ==>
       gas_origin_ptr_path (cx_dead H ^cx,0,^explicit,^ctx,fn,[])
         (s,FEMPTY,entry_taint) marks (OK u,Gu,tu)` by
    (rpt gen_tac >> strip_tac >>
     irule (SIMP_RULE bool_ss [APPEND] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_origin_ptr_path_append))) >>
     qexistsl_tac [`Gh`,`hit`,`(OK hit,Gh,thit)`,`thit`] >> simp_tac bool_ss [] >>
     conj_tac >- simp[] >>
     first_assum (fn th => mp_tac (Q.SPEC `H` th) >> disch_then drule >> disch_then ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (hit,Gh,thit) marks _`
    (qspec_then `^empty_h` (drule_then assume_tac)) >>
  qpat_assum `gas_origin_ptr_path _ (hit,Gh,thit) marks _`
    (map_every assume_tac o CONJUNCTS o MATCH_MP gas_origin_ptr_path_projections) >>
  drule_then (strip_assume_tac o SIMP_RULE bool_ss []) gas_path_ptr_erase >>
  `u.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,FEMPTY,entry_taint) marks _`
       (qspec_then `^empty_h` (drule_then assume_tac)) >>
     qpat_assum `gas_origin_ptr_path _ (s,FEMPTY,entry_taint) marks _`
       (assume_tac o CONJUNCT2 o MATCH_MP gas_origin_ptr_path_projections) >>
     qpat_assum `gas_path_ptr _ _ _ _ _ _ _ s _ _ _ (OK u)`
       (strip_assume_tac o SIMP_RULE bool_ss [] o MATCH_MP (SPEC_ALL gas_path_ptr_erase)) >>
     qpat_assum `gas_path _ _ s _ (OK u)`
       (mp_tac o MATCH_MP (SPEC_ALL grouped_cut_call_ctx)) >>
     qpat_assum `s = _` (fn th => simp_tac (srw_ss()) [th])) >>
  suspend "cut_bounds"
QED

Resume grouped_default_route_elim_with_init_layout[cut_bounds]:
  qpat_assum `ci_mono sd entry` (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ci_mono_def]) >>
  `groups = MAP (package_external_group tops rpolicy.rpol_target T
    (K global_nonreentrant_slot)) (FST (classify_functions tops))` by
    (qpat_assum `classify_functions tops = _` (fn th => simp_tac bool_ss [th,FST]) >>
     first_assum ACCEPT_TAC) >>
  `fresh_label "fallback" (initial_compile_state "__entry") = (sn.cs_current_bb,sf)` by
    (sym_tac >> first_assum ACCEPT_TAC) >>
  `!i. MEM i (state_insts sb) ==>
    i.inst_opcode <> INVOKE /\ (i.inst_opcode = ALLOCA ==> i.inst_id < entry.cs_next_id) /\
    EVERY (not_fresh_at entry) i.inst_outputs` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fresh_label "fallback" _ = (sn.cs_current_bb,sf)`,
        `groups = MAP _ (FST (classify_functions tops))`,
        `check_contract F am.layouts tx.target [(NONE,tops)] = SOME art`,
        `compile_group_dispatch_linear groups _ sf = (_,sd)`,
        `cs_extends sb sd`, `sd.cs_next_var <= entry.cs_next_var`,
        `sd.cs_next_id <= entry.cs_next_id`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[grouped_cut_instruction_bounds]) >>
  `?G. callees_stable G ^ctx fn` by
    (irule ctx_entry_callees_stable >> conj_tac
     >- (qspecl_then [`tops`,`rpolicy`,`unit`] mp_tac lower_vyper_runtime_unit_fns_stable >>
         impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `"__entry"` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `no_phi_fn fn` by
    (simp_tac bool_ss [no_phi_fn_def,EVERY_MEM] >> first_assum ACCEPT_TAC) >>
  qpat_assum `ci_mono si entry` (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ci_mono_def]) >>
  `cenv_ptrs_below 0 ^ce /\ (^ce).ce_ctor_exit_label = NONE` by
    (qspecl_then [`tops`,`T`,`K global_nonreentrant_slot`,`rpolicy.rpol_target`,
       `(mut,nr,^rr,tx.function_name,args,^ds,ret,^ss)`] mp_tac package_external_fn_ok >>
     qpat_assum `^defaults_pkg = _` (fn th => simp_tac bool_ss [th,FST,SND])) >>
  `cenv_ptrs_below entry.cs_next_var ^ce` by
    (irule fragFuelStmtBaseTheory.cenv_ptrs_below_le >> qexists_tac `0` >> simp[]) >>
  `cenv_ptrs_below entry.cs_next_var (compile_register_kwarg_vars ^ce vars)` by
    (irule (cj 2 compile_register_kwarg_vars_ptrs) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp_tac bool_ss [EVERY_MEM,pairTheory.FORALL_PROD,FST,SND] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!name op ty e. MEM (name,op,ty,e) vars ==> _` (drule_then strip_assume_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`not_fresh_at si _`, `si.cs_next_var <= entry.cs_next_var`, `_ = Var _`, `_ = Var _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[var_below_def,not_fresh_at_def] >>
     rpt strip_tac >> `si.cs_next_var <= n` by decide_tac >> gvs[]) >>
  suspend "bounds_finish"
QED

Resume grouped_default_route_elim_with_init_layout[bounds_finish]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (t,J,tz) marks _ /\ _`
    (qspec_then `^empty_h` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `at_point sb u` by
    (simp_tac bool_ss [at_point_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `at_point checks hit /\ fresh_vars_wrt entry hit /\
    (!id p. FLOOKUP hit.vs_allocas id = SOME p ==> id < entry.cs_next_id)` by
    (qpat_assum `selected_registration_resources _ _ _ 0 checks hit` mp_tac >>
     qpat_assum `ci_mono checks entry` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[selected_registration_resources_def,ci_mono_def,at_point_def] >> rpt strip_tac
     >- (irule fresh_vars_wrt_mono >> qexists_tac `checks` >> simp[]) >>
     irule LESS_LESS_EQ_TRANS >> qexists_tac `checks.cs_next_id` >> simp[]) >>
  `fresh_vars_wrt entry u /\
    (!aid pair. FLOOKUP u.vs_allocas aid = SOME pair ==> aid < entry.cs_next_id)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`compile_entry_checks _ _ checks = ((),si)`, `compile_init_kwargs _ vars _ _ _ si = ((),sb)`,
        `fn_has_code checks sb fn`, `at_point checks hit`, `checks.cs_current_insts = []`,
        `at_point sb u`, `gas_path _ fn hit _ (OK u)`, `emit_inst JMP [Label entry.cs_current_bb] [] sb = _`,
        `fn_has_code sb term fn`, `cs_extends term entry`, `entry.cs_current_insts = []`,
        `(^ce).ce_ctor_exit_label = NONE`, `cenv_ptrs_below _ (compile_register_kwarg_vars ^ce vars)`,
        `compile_register_positional_args (compile_register_kwarg_vars ^ce vars) _ 4 entry = (ce,sa)`,
        `compile_guarded_body ce _ _ _ _ _ _ sa = ((),done)`, `fn_has_code entry done fn`,
        `cs_extends sb done`, `ALL_DISTINCT (MAP _ (all_blocks done))`, `no_phi_fn fn`,
        `callees_stable G ^ctx fn`, `fresh_vars_wrt entry hit`,
        `!id pair. FLOOKUP hit.vs_allocas id = SOME pair ==> id < entry.cs_next_id`,
        `!i. MEM i (state_insts sb) ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule_all_then ACCEPT_TAC
       (Q.INST [`limit` |-> `entry`] (SPEC_ALL grouped_initializer_before_common_bounds))) >>
  `fresh_vars_wrt sa u` by
    (irule fresh_vars_wrt_mono >> qexists_tac `entry` >> reverse conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_assum `ci_mono entry sa` (mp_tac o PURE_REWRITE_RULE [ci_mono_def]) >>
     simp_tac (srw_ss()) [arithmeticTheory.GREATER_EQ]) >>
  suspend "decode_finish"
QED

Resume grouped_default_route_elim_with_init_layout[decode_finish]:
  `EVERY cd_cast_domain tvs` by
    (qpat_assum `OPT_MMAP (evaluate_type _) (MAP SND args) = SOME tvs`
       (ACCEPT_TAC o MATCH_MP evaluate_types_cd_cast_domain)) >>
  `LIST_REL value_has_type (TAKE ^pos tvs) (TAKE ^pos tx.args)` by
    (`EVERY cd_cast_domain (TAKE ^pos tvs)` by
       (irule EVERY_TAKE >> first_assum ACCEPT_TAC) >>
     qpat_assum `calldata_decode_args ^cd (TAKE ^pos tvs) 0 = _` mp_tac >>
     qpat_assum `EVERY cd_cast_domain (TAKE ^pos tvs)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule_all calldata_decode_args_safe_cast >> match_mp_tac LIST_REL_mono >>
     metis_tac[safe_cast_result_well_typed]) >>
  `LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs` by
    (qpat_assum `OPT_MMAP (evaluate_type _) (MAP SND args) = SOME tvs`
       (ACCEPT_TAC o MATCH_MP OPT_MMAP_LIST_REL)) >>
  `EVERY (\tv. type_memory_size tv < dimword (:256)) tvs` by
    (simp_tac bool_ss [EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
     `i < LENGTH args` by simp[] >>
     qpat_assum `!i. i < LENGTH args ==> _` (drule_then (ACCEPT_TAC o cj 2))) >>
  `!c arg tv. MEM (arg,tv) (ZIP (args,tvs)) /\ c = ^ce with ce_vars := c.ce_vars ==>
     selected_slot_accepts c (type_env tops) c.ce_struct_fields (SND arg) tv /\
     abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv` by
    (qpat_assum `LENGTH tvs = LENGTH args`
       (fn th => simp_tac (srw_ss()) [MEM_ZIP,th]) >> rpt gen_tac >>
     disch_then (map_every strip_assume_tac o CONJUNCTS) >>
     `abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv` by
       (qpat_assum `c = _` SUBST1_TAC >> simp_tac (srw_ss()) [ctor_decoder_coherent_vars] >>
        qpat_assum `arg = _` SUBST1_TAC >> qpat_assum `tv = _` SUBST1_TAC >>
        qpat_assum `!i. i < LENGTH args ==> _` (drule_then (ACCEPT_TAC o cj 1))) >>
     conj_tac >- (irule selected_register_one >> irule selected_argument_decoder_accepts >>
                  first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\arg tv. type_memory_bytes ^ce (SND arg) = type_memory_size tv)
    (TAKE ^pos args) (TAKE ^pos tvs)` by
    (irule LIST_REL_TAKE >>
     qpat_assum `LIST_REL (\arg tv. abi_decoder_coherent _ _ _ (SND arg) tv) args tvs` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp_tac bool_ss [] >> rpt gen_tac >> disch_tac >>
     drule abi_decoder_coherent_header >> simp_tac (srw_ss()) [abi_decoder_header_def] >>
     metis_tac[]) >>
  suspend "slot_finish"
QED

Resume grouped_default_route_elim_with_init_layout[slot_finish]:
  qpat_assum `ci_mono sb entry` (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ci_mono_def]) >>
  `ALL_DISTINCT (MAP (\(_,op,_,_). op) vars)` by
    (qpat_assum `compile_create_kwarg_allocas ^ce specs _ = (vars,_)`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (SPEC_ALL grouped_keyword_allocations_distinct))) >>
  `LIST_REL (\(name,dst,ty,e) (aid,q,p,tv). dst = Var q /\
     type_memory_bytes ^ce ty = type_memory_size tv /\
     MEM (mk_inst aid ALLOCA [Lit (n2w (type_memory_size tv))] [q]) (fn_insts fn)) vars slots` by
    (qpat_assum `LIST_REL (\(_,op,_,_) (_,q,_,_). op = Var q /\ _) vars slots` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp_tac (srw_ss()) [pairTheory.FORALL_PROD]) >>
  `LIST_REL (\(aid,q,p,tv) v. aid < sb.cs_next_id /\ not_fresh_at entry q /\
     FLOOKUP u.vs_allocas aid = SOME (p,type_memory_size tv) /\ lookup_var q u = SOME (n2w p) /\
     ptr_covers Gu tu q u (type_memory_size tv) /\ value_has_type tv v /\
     (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory tv v p mem))
     slots (DROP ^pos tx.args ++ values)` by
    (qpat_assum `LIST_REL _ slots (DROP _ tx.args ++ values)` mp_tac >>
     simp_tac bool_ss [subst_consts_exprs_length] >> match_mp_tac LIST_REL_mono >>
     simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >> rpt conj_tac >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sb` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP (\(_,_,_,tv). tv) slots = DROP ^pos tvs` by
    (qpat_assum `MAP _ slots = DROP _ tvs` (ACCEPT_TAC o REWRITE_RULE [subst_consts_exprs_length])) >>
  `MAP (\(name,_,ty,_). (name,ty)) vars = DROP ^pos args` by
    (qpat_assum `MAP _ vars = DROP _ args` (ACCEPT_TAC o REWRITE_RULE [subst_consts_exprs_length])) >>
  suspend "source_finish"
QED

Resume grouped_default_route_elim_with_init_layout[source_finish]:
  `EVERY external_defaults_no_sha256 externals` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`lower_vyper_runtime_unit tops rpolicy = SOME unit`,
        `classify_functions tops = (externals,_,_,_)`,
        `EXISTS external_has_defaults externals`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[] >>
     gvs[lower_vyper_runtime_unit_def,AllCaseEqs()]) >>
  `no_sha256_exprs dflts` by
    (qpat_assum `MEM (mut,nr,^rr,tx.function_name,args,^ds,ret,^ss) (FST (classify_functions tops))` mp_tac >>
     qpat_assum `classify_functions tops = _` (fn th => simp_tac bool_ss [th,FST]) >>
     qpat_assum `EVERY external_defaults_no_sha256 externals`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[external_defaults_no_sha256_def,cj 3 source_no_sha256_after_const_substitution]) >>
  `no_sha256_exprs (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)` by
    (pure_rewrite_tac[no_sha256_collections] >> irule EVERY_DROP >>
     qpat_assum `no_sha256_exprs dflts` (ACCEPT_TAC o REWRITE_RULE [no_sha256_collections])) >>
  `EVERY (runtime_constant_expr [(NONE,tops)])
     (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)` by
    (irule EVERY_DROP >> first_assum ACCEPT_TAC) >>
  `4 + SUM (MAP tv_abi_size (TAKE ^pos tvs)) < dimword (:256)` by
    (qpat_assum `fullcd < dimword (:256)` mp_tac >>
     qpat_assum `fullcd = _` (fn th => simp_tac bool_ss [th]) >>
     qspec_then `^pos` (qspec_then `tvs` (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))) TAKE_DROP >>
     simp[MAP_APPEND,SUM_APPEND]) >>
  suspend "enter"
QED

Resume grouped_default_route_elim_with_init_layout[enter]:
  `!H. valid_horizon ^cx (initial_state am []) H ee.storage_trace ==>
    gas_origin_ptr_path (cx_dead H ^cx,0,^explicit,^ctx,fn,[]) (s,FEMPTY,entry_taint) marks (OK u,Gu,tu) /\
    stmt_state_rel H ^ctx fn ^c0 ^cx (ee with gas_obs := []) u /\
    ghost_inv_at (cx_dead H ^cx) 0 NONE ^c0 ^cx (ee with gas_obs := []) Gu tu u` by
    (gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,FEMPTY,entry_taint) marks _`
           (drule_then ACCEPT_TAC)) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (t,J,tz) marks _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> conj_tac >> first_assum ACCEPT_TAC) >>
  irule (INST_TYPE [``:'a`` |-> ``:expr``] grouped_default_normal_bound_entry) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `art` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `fbody` >> conj_tac >- REFL_TAC >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gu`,`bb`,`ce`,`^ce`,`common`,`^ctx`,`sb`,`^cx`,`ee`,`entries`,`entry`,
    `^explicit`,`done`,`fn`,`key`,`DROP ^pos args`,`DROP ^pos tvs`,`DROP ^pos tx.args ++ values`,
    `lbl`,`marks`,`mc`,`off`,`pa`,`pay`,`TAKE ^pos args`,`TAKE ^pos tvs`,`TAKE ^pos tx.args`,
    `rt`,`s`,`ev`,`sa`,`sf`,`shdone`,`shfn`,`shsa`,`shadow_unit`,`ARB:instruction`,`slots`,
    `specs`,`term`,`tu`,`u`,`ut`,`values`,`vars`,`view`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [TAKE_DROP,listTheory.APPEND_ASSOC] >> TRY (first_assum ACCEPT_TAC)
  >- (sym_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `LENGTH tvs = LENGTH args`
        (fn th => simp_tac bool_ss [LENGTH_TAKE_EQ,th])) >>
  qpat_assum `u.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Finalise grouped_default_route_elim_with_init_layout

Theorem grouped_default_route_elim:
  ^route_inputs ==> ^reject_handler ==> ^init_handler ==>
  ^selected_endpoint \/ ^route_exit
Proof
  disch_then (assume_tac o MATCH_MP grouped_default_route_elim_with_init_layout) >>
  disch_tac >> disch_tac >>
  qpat_x_assum `^reject_handler ==> _` (drule_then irule) >>
  let val names = map (fn v => [ANTIQUOTE v]) init_binders in
    map_every qx_gen_tac names >> disch_tac >> disch_tac >>
    qpat_assum `^init_handler` (qspecl_then names mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
  end
QED

Theorem grouped_default_call_route:
  ^route_inputs ==>
  ^selected_endpoint \/
  (?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
      tops ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail. FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading"))))
Proof
  disch_then (mp_tac o MATCH_MP
    (Q.INST [`route_exit` |-> `^initializer_exit`] grouped_default_route_elim)) >>
  impl_tac
  >- (rpt gen_tac >>
      disch_then (strip_assume_tac o MATCH_MP grouped_entry_value_rejected) >>
      qexists_tac `[]` >> simp[gas_explicit_def]) >>
  impl_tac
  >- (rpt gen_tac >>
      disch_then (ACCEPT_TAC o MATCH_MP grouped_default_passing_execution)) >>
  simp[]
QED
