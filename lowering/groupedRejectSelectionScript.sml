(* Select the grouped entry and certify its initializer cut. *)
Theory groupedRejectSelection
Ancestors
  e2eDefs ptrDiscipline loweringShapeProps acceptedContextPhi compileVyper fragGasOriginPtr list
  pred_set venomInst venomState entryRejectAllocationIds entryChecksRejectJoint
  groupedDispatchPath groupedEntryResources callRejectMemory[ignore_grammar]
  groupedSelectedDefault groupedRuntimeBodyCode groupedEntryPackage groupedDefaultArguments
  checkedSelectorTableProps groupedKeywordDecode venomExecProofs calldataSelectorProps
  exprLoweringProps selectedAcceptedFold abiDecoderCoherence compileEnv vyperContext
  gasShadowModuleDefs groupedInternalLabels vyperABIEntries vyperCompiler entryRejectCode
  entryCodeOwnership emitHelperProps fragGasOriginPtrLoop fragFuel finite_map rich_list words
  pair arithmetic runtimeDefaultRejectExpr groupedEntryCounters loweringShapeDefs relation
  vyperAST rejectPrefixSourceShape loweringShapeRules groupedRejectCutObserver
Libs
  runtimeDefaultRejectSyntaxLib groupedRejectCutLib

val _ = Parse.hide "tops";

Theorem row22_group_selection[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  source_typing_ok tops am tx /\
  package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off /\
  groups = MAP (package_external_group tops rp.rpol_target T (K global_nonreentrant_slot))
    (FST (classify_functions tops)) /\
  groups = pre ++ ExternalDefaults common entries specs off::post /\
  MEM (prefix,k) (abi_entries args defaults) /\
  abi_method_id (type_env tops) name (MAP SND prefix) = cd_selector cd /\
  4 <= LENGTH cd ==>
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => calldata_method_id cd <> n2w sel
  | ExternalDefaults comp ens sp _ =>
      FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) ens = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pre /\
  FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) entries =
    SOME (cd_selector cd,external_prefix_label name k,min_calldata_size common.ec_env prefix 0,k) /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[source_typing_ok_def] >>
  `ALL_DISTINCT (MAP FST (grouped_selectors groups)) /\
   EVERY (\(sel,_,_). sel < dimword (:256)) (grouped_selectors groups)` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >>
     simp[packaged_grouped_selector_width] >>
     metis_tac[check_contract_grouped_selectors_distinct]) >>
  `EVERY (\group. case group of ExternalSingle _ _ => T
    | ExternalDefaults comp ens sp _ =>
        EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) groups` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >>
     Cases_on `classify_functions tops` >> PairCases_on `r` >>
     drule_all checked_grouped_package_keyword_widths >> simp[]) >>
  drule_all grouped_default_entry_member >> strip_tac >>
  drule cd_selector_method_id >> strip_tac >>
  `MEM (w2n (calldata_method_id cd),external_prefix_label name k,
        min_calldata_size common.ec_env prefix 0,k) entries` by metis_tac[] >>
  qpat_x_assum `groups = pre ++ _` SUBST_ALL_TAC >>
  drule_all grouped_default_selector_route >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[EVERY_APPEND] >> simp[EVERY_MEM] >> qx_gen_tac `g` >> strip_tac >>
  qpat_assum `EVERY (\group. case group of ExternalSingle _ _ => _ | ExternalDefaults _ es _ _ => FIND _ es = NONE) pre`
    (drule_then mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  qpat_assum `EVERY (\group. case group of ExternalSingle _ _ => T | ExternalDefaults _ _ _ _ => _) pre`
    (drule_then mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  Cases_on `g` >- (rename1 `ExternalSingle sel _` >> PairCases_on `sel` >> simp[]) >>
  simp[EVERY_MEM]
QED


Theorem row22_common_interval[local]:
  MEM (ExternalCommonJob common vars) jobs /\
  compile_external_jobs jobs sd = ((),sx) /\
  EVERY group_job_label_ok jobs /\ cs_extends sx se /\
  (!bb. MEM bb (all_blocks se) ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb) ==>
  ?entry ce registered. ci_mono sd entry /\ entry.cs_current_bb = common.ec_common_label /\
    entry.cs_current_insts = [] /\
    compile_register_positional_args
      (compile_register_kwarg_vars common.ec_env vars) common.ec_pos_args 4 entry = (ce,registered) /\
    fn_has_code entry registered fn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `MEM _ jobs` (qx_choosel_then [`pre`,`post`] assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  qpat_x_assum `jobs = _` SUBST_ALL_TAC >>
  drule_all compile_external_common_job_interval >>
  disch_then (qx_choosel_then [`start`,`entry`,`ce`,`registered`,`done`] strip_assume_tac) >>
  qexistsl_tac [`entry`,`ce`,`registered`] >> simp[] >> rpt conj_tac
  >- (irule ci_mono_trans >> qexists_tac `start` >>
      metis_tac[compile_external_jobs_ci_mono, ci_mono_new_block, SND])
  >- metis_tac[new_block_props]
  >- metis_tac[new_block_props] >>
  irule fn_has_code_retained_interval >> simp[] >> qexists_tac `se` >>
  simp[] >> metis_tac[cs_extends_trans]
QED


Theorem row22_nonpayable_origin[local]:
  compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
  fn_has_code sf sd fn /\ EVERY group_entry_labels_ok groups /\
  groups = pre ++ ExternalDefaults common entries specs off::post /\
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => calldata_method_id s.vs_call_ctx.cc_calldata <> n2w sel
  | ExternalDefaults comp es sp _ =>
      FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel) es = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pre /\
  FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel) entries =
    SOME (sel,lbl,mincd,k) /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  mincd < dimword (:256) /\ ~common.ec_payable /\ s.vs_call_ctx.cc_callvalue <> 0w /\
  selected_registration_resources ctx fn site 0 sf s /\ s.vs_allocas = FEMPTY /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?z Hz tz. z.vs_returndata = [] /\
    !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[])
      (s,FEMPTY,entry_taint) [] (Abort Revert_abort z,Hz,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_dispatch_long_prelude >>
  disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`] strip_assume_tac) >>
  qpat_x_assum `groups = pre ++ _` SUBST_ALL_TAC >>
  drule_all compile_external_groups_selected_default_origin >>
  disch_then (qspecl_then [`[]`,`G'`] strip_assume_tac) >>
  rename1 `compile_entry_checks mincd common.ec_payable checks = ((),init)` >>
  rename1 `selected_registration_resources ctx fn site 0 checks hit` >>
  `hit.vs_call_ctx = s.vs_call_ctx` by fs[selected_registration_frame_def] >>
  qpat_assum `selected_registration_resources ctx fn site 0 checks hit`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  mp_tac (Q.INST [`m` |-> `mincd`,`pay` |-> `common.ec_payable`,
    `st` |-> `checks`,`last` |-> `init`,`s` |-> `hit`, `lo` |-> `0`,`PG` |-> `[]`,
    `G` |-> `G''`,`tn` |-> `tn''`] (SPEC_ALL compile_entry_checks_reject_joint)) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
  strip_tac >> qexistsl_tac [`z`,`H`,`u`] >> simp[] >>
  gen_tac >> metis_tac[gas_origin_ptr_path_trans, APPEND_NIL]
QED


Triviality row22_dispatch_layout_bounds:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  groups = MAP (package_external_group tops rp.rpol_target T (K global_nonreentrant_slot))
    (FST (classify_functions tops)) /\
  run_grouped_lowering groups ips fb rp "__entry" = SOME u /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME fn /\
  fresh_label "fallback" (initial_compile_state "__entry") = (fallback,sf) /\
  compile_group_dispatch_linear groups fallback sf = (jobs,sd) ==>
  state_insts sf = [] /\ shape_state sd /\ no_phi_fn fn /\
  ?final. cs_extends sd final /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks final))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule run_grouped_lowering_context >> strip_tac >>
  drule_all run_grouped_lowering_dispatch_code >>
  disch_then (qx_choosel_then [`sf'`,`fallback'`,`jobs'`,`sd'`,`sx'`,`sn'`,`final`]
    (map_every assume_tac o CONJUNCTS)) >>
  `sf' = sf /\ fallback' = fallback` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `sf' = sf` SUBST_ALL_TAC >>
  qpat_x_assum `fallback' = fallback` SUBST_ALL_TAC >>
  `jobs' = jobs /\ sd' = sd` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `jobs' = jobs` SUBST_ALL_TAC >>
  qpat_x_assum `sd' = sd` SUBST_ALL_TAC >>
  `state_insts sf = []` by
    gvs[fresh_label_def, initial_compile_state_def, state_insts_def, all_blocks_def] >>
  `shape_state sd` by
    (mp_tac (Q.SPECL [`F`,`jump_label_ok`,`\st. T`,`"fallback"`] shape_step_fresh_label_sfx) >>
     simp[shape_stable_def, shape_step_def] >>
     disch_then (qspecl_then [`initial_compile_state "__entry"`,`fallback`,`sf`] mp_tac) >>
     simp[shape_state_initial_compile_state] >> strip_tac >>
     `jump_label_ok fallback /\ ~label_sfx "dispatch" fallback` by
       (simp[jump_label_ok_def] >> strip_tac >>
        mp_tac (Q.INST [`s1` |-> `"fallback"`,`s2` |-> `"dispatch"`,
                        `l1` |-> `fallback`,`l2` |-> `fallback`] label_sfx_distinct) >> simp[]) >>
     drule_all checked_group_dispatch_shape >> simp[]) >>
  `no_phi_fn fn` by
    (drule lowering_context_ok_bridge >> strip_tac >>
     `ALL_DISTINCT (fn_labels fn)` by (drule lookup_function_MEM >> fs[EVERY_MEM]) >>
     simp[no_phi_fn_def, EVERY_MEM] >> rpt strip_tac >>
     irule lowering_context_ok_block_phi >> metis_tac[MEM_lookup_block, fn_labels_def]) >>
  simp[] >> metis_tac[]
QED

Triviality row22_selected_initializer_syntax:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  lower_vyper_runtime_unit tops rp = SOME u /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions tops)) /\
  package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off /\
  compile_create_kwarg_allocas common.ec_env specs alloc_start = (vars,alloc_end) ==>
  EVERY (\(_,_,_,e). runtime_constant_expr [(NONE,tops)] e /\
    ~supported_expr_exists (^checked_default_expr common.ec_env) e) vars /\
  acyclic_struct_metadata common.ec_env.ce_struct_fields
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY external_defaults_no_sha256 (FST (classify_functions tops))` by
    (qpat_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
     Cases_on `classify_functions tops` >> PairCases_on `r` >>
     gvs[lower_vyper_runtime_unit_def, LET_THM, bool_case_eq]) >>
  `no_sha256_exprs defaults` by
    (qpat_assum `EVERY external_defaults_no_sha256 _`
      (drule_then mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[external_defaults_no_sha256_def]) >>
  drule_all (BETA_RULE runtime_default_checked_package) >> strip_tac >>
  drule compile_create_kwarg_allocas_preserves_specs >> strip_tac >>
  simp[] >> qpat_x_assum `EVERY _ specs` mp_tac >>
  qpat_assum `MAP _ vars = specs` (SUBST1_TAC o SYM) >>
  simp[EVERY_MAP] >> match_mp_tac EVERY_MONOTONIC >> simp[pairTheory.FORALL_PROD]
QED

Theorem row22_selected_start_with_cut:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  (ctx_has_dalloca u.cu_context ==> unit_alloca_budget u.cu_context <= w2n vs.vs_initial_fmp) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions tops)) /\
  defaults <> [] /\ MEM (prefix,k) (abi_entries args defaults) /\
  abi_method_id (type_env tops) name (MAP SND prefix) = cd_selector vs.vs_call_ctx.cc_calldata /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND prefix) = SOME tvs /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
  start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> ==>
  (?fn z H tn. lookup_function "__entry" u.cu_context.ctx_functions = SOME fn /\
    z.vs_returndata = [] /\
    !D. gas_origin_ptr_path (D,0,EMPTY,u.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (Abort Revert_abort z,H,tn)) \/
  (?fn shadow_unit shadow_fn common entries specs off all_tvs
    vars alloc_start alloc_end checks si cut last dispatch_end shadow_si shadow_cut
    v Gv tnv t J tz entry ce registered.
    lookup_function "__entry" u.cu_context.ctx_functions = SOME fn /\
    runtime_gas_shadow_unit tops rp = SOME shadow_unit /\
    gas_shadow_unit u shadow_unit /\
    lookup_function "__entry" shadow_unit.cu_context.ctx_functions = SOME shadow_fn /\
    gas_shadow_function fn shadow_fn /\
    package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
      (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off /\
    ALL_DISTINCT (MAP FST args) /\
    OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME all_tvs /\
    LIST_REL (\(n,ty) tv.
      abi_decoder_coherent common.ec_env (type_env tops) common.ec_env.ce_struct_fields ty tv /\
      (?loc. FLOOKUP common.ec_env.ce_vars n = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args all_tvs /\
    prefix = TAKE (LENGTH args - LENGTH defaults + k) args /\
    tvs = TAKE (LENGTH args - LENGTH defaults + k) all_tvs /\
    4 + SUM (MAP tv_abi_size all_tvs) < dimword (:256) /\
    4 + SUM (MAP tv_abi_size tvs) = min_calldata_size common.ec_env prefix 0 /\
    off = 4 + SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH defaults) all_tvs)) /\
    specs = MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP (LENGTH args - LENGTH defaults) args,defaults)) /\
    common.ec_pos_args = build_positional_args common.ec_env (TAKE (LENGTH args - LENGTH defaults) args) /\
    (common.ec_payable \/ start.vs_call_ctx.cc_callvalue = 0w) /\
    compile_create_kwarg_allocas common.ec_env specs alloc_start = (vars,alloc_end) /\
    checks.cs_current_bb = external_prefix_label name k /\ checks.cs_current_insts = [] /\
    compile_entry_checks (min_calldata_size common.ec_env prefix 0) common.ec_payable checks = ((),si) /\
    fn_has_code checks si fn /\
    compile_init_kwargs common.ec_env vars off k (Lit 0w) si = ((),cut) /\
    fn_has_code si cut fn /\ fn_has_code cut last fn /\
    emit_inst JMP [Label common.ec_common_label] [] cut = ((),last) /\
    ci_mono last dispatch_end /\
    compile_init_kwargs common.ec_env
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
      off k (Lit 0w) shadow_si = ((),shadow_cut) /\
    fn_has_code shadow_si shadow_cut shadow_fn /\ gas_shadow_state si shadow_si /\
    selected_registration_resources u.cu_context fn ARB 0 checks v /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,u.cu_context,fn,[])
      (v,Gv,tnv) [] (OK t,J,tz)) /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,u.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK v,Gv,tnv)) /\
    selected_registration_resources u.cu_context fn ARB 0 si t /\
    selected_registration_frame start entry_taint t tz /\ t.vs_memory = start.vs_memory /\
    (!name op ty e. MEM (name,op,ty,e) vars ==>
      ?id q base. op = Var q /\ not_fresh_at si q /\ lookup_var q t = SOME (n2w base) /\
        MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q]) (fn_insts fn) /\
        FLOOKUP t.vs_allocas id = SOME (base,type_memory_bytes common.ec_env ty) /\
        id < si.cs_next_id /\ base + type_memory_bytes common.ec_env ty < dimword (:256) /\
        ptr_covers J tz q t (type_memory_bytes common.ec_env ty)) /\
    (ctx_has_dalloca u.cu_context ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,u.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK t,J,tz)) /\
    fn_inst_ids_distinct fn /\ unit_alloca_budget u.cu_context < dimword (:256) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
    ci_mono cut entry /\ entry.cs_current_bb = common.ec_common_label /\ entry.cs_current_insts = [] /\
    compile_register_positional_args (compile_register_kwarg_vars common.ec_env vars)
      common.ec_pos_args 4 entry = (ce,registered) /\ fn_has_code entry registered fn /\
    ^row22_cut_facts u.cu_context fn cut t entry)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  fs[pairTheory.FST] >>
  drule_all lower_grouped_runtime_pair >>
  disch_then (qx_choosel_then [`groups`,`ips`,`fall`,`model`,`fn`,`bb`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all grouped_shadow_entry_dispatch >>
  disch_then (qx_choosel_then [`shadow_unit`,`shadow_fn`,`sf`,`fallback`,`jobs`,`sd`,
    `shd`,`sx`,`shx`,`sn`,`shn`,`se`,`she`] (map_every assume_tac o CONJUNCTS)) >>
  `shadow_unit = model` by metis_tac[optionTheory.SOME_11] >> pop_assum SUBST_ALL_TAC >>
  `groups = MAP (package_external_group tops rp.rpol_target T (K global_nonreentrant_slot))
    (FST (classify_functions tops))` by simp[] >>
  `MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions tops))` by fs[] >>
  qabbrev_tac `pk = package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,defaults,ret,stmts)` >>
  `?common entries specs off. pk = ExternalDefaults common entries specs off` by
    (simp[Abbr `pk`, package_external_group_def, LET_THM, NULL_EQ] >> pairarg_tac >> gvs[]) >>
  `MEM pk groups` by
    (qpat_assum `groups = MAP _ (FST _)` SUBST1_TAC >> simp[MEM_MAP] >>
     qexists_tac `(mut,nr,rr,name,args,defaults,ret,stmts)` >> simp[Abbr `pk`]) >>
  pop_assum (qx_choosel_then [`pre`,`post`] assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  `package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off /\
   groups = pre ++ ExternalDefaults common entries specs off::post` by
    metis_tac[markerTheory.Abbrev_def] >> pop_assum strip_assume_tac >>
  `4 <= LENGTH vs.vs_call_ctx.cc_calldata` by decide_tac >>
  drule_all row22_group_selection >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_defaults_argument_metadata >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `all_tvs` strip_assume_tac)) >>
  suspend "metadata"
QED

Resume row22_selected_start_with_cut[metadata]:
  `prefix = TAKE (LENGTH args - LENGTH defaults + k) args` by fs[abi_entries_member] >>
  `tvs = TAKE (LENGTH args - LENGTH defaults + k) all_tvs` by
    (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME all_tvs`
       (qspec_then `LENGTH args - LENGTH defaults + k` mp_tac o MATCH_MP opt_mmap_take_some) >>
     qpat_assum `prefix = TAKE _ args` (fn eq =>
       qpat_assum `OPT_MMAP _ (MAP SND prefix) = SOME tvs`
         (mp_tac o REWRITE_RULE [eq, MAP_TAKE])) >> simp[]) >>
  `LIST_REL (\arg tv. abi_decoder_coherent common.ec_env (type_env tops)
      common.ec_env.ce_struct_fields (SND arg) tv) args all_tvs` by
    (qpat_assum `LIST_REL _ args all_tvs` mp_tac >> ho_match_mp_tac LIST_REL_mono >> Cases >> simp[]) >>
  `4 + SUM (MAP tv_abi_size tvs) = min_calldata_size common.ec_env prefix 0` by
    metis_tac[grouped_argument_min_calldata_size] >>
  drule_all grouped_default_entry_member >> strip_tac >>
  `off = 4 + SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH defaults) all_tvs))` by
    metis_tac[grouped_argument_min_calldata_size] >>
  `common.ec_pos_args = build_positional_args common.ec_env (TAKE (LENGTH args - LENGTH defaults) args)` by
    (Cases_on `set_external_package_target rp.rpol_target
       (package_external_fn tops T (K global_nonreentrant_slot)
         (mut,nr,rr,name,args,defaults,ret,stmts))` >> PairCases_on `r` >>
     drule_all grouped_package_common_environment >> simp[]) >>
  drule_all (Q.INST [`site` |-> `ARB`] (SPEC_ALL grouped_dispatch_initial_resources)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `start.vs_call_ctx = vs.vs_call_ctx` by simp[] >>
  `4 <= LENGTH start.vs_call_ctx.cc_calldata` by simp[] >>
  `min_calldata_size common.ec_env prefix 0 <= LENGTH start.vs_call_ctx.cc_calldata` by
    (qpat_assum `start.vs_call_ctx = _` SUBST1_TAC >> decide_tac) >>
  `min_calldata_size common.ec_env prefix 0 < dimword (:256)` by decide_tac >>
  Cases_on `common.ec_payable \/ start.vs_call_ctx.cc_callvalue = 0w` >- suspend "pass" >>
  suspend "nonpayable"
QED

Resume row22_selected_start_with_cut[pass]:
  disj2_tac >>
  `EVERY group_entry_labels_ok (MAP
    (\group. case group of
      ExternalSingle selector package => ExternalSingle selector (gas_shadow_external_package package)
    | ExternalDefaults common entries specs off =>
        ExternalDefaults (common with ec_body := MAP gas_shadow_stmt common.ec_body)
          entries (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off) groups)` by
    (simp[NoAsms, EVERY_MAP, EVERY_MEM] >> qx_gen_tac `group` >> strip_tac >>
     qpat_assum `EVERY group_entry_labels_ok groups`
       (drule_then mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `group` >- (rename1 `ExternalSingle sel pkg` >> PairCases_on `sel` >>
       PairCases_on `pkg` >> simp[group_entry_labels_ok_def,gas_shadow_external_package_def]) >>
     simp[group_entry_labels_ok_def]) >>
  Q.SUBGOAL_THEN `min_calldata_size common.ec_env prefix 0 <= 4 \/
    min_calldata_size common.ec_env prefix 0 <= LENGTH start.vs_call_ctx.cc_calldata` ASSUME_TAC
  >- (DISJ2_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `start.vs_call_ctx = vs.vs_call_ctx`
    (fn eq => qpat_assum `FIND _ entries = SOME _` (assume_tac o PURE_REWRITE_RULE [GSYM eq])) >>
  qpat_assum `start.vs_call_ctx = vs.vs_call_ctx`
    (fn eq => qpat_assum `EVERY _ pre` (assume_tac o PURE_REWRITE_RULE [GSYM eq])) >>
  drule_all (Q.INST [`PG` |-> `[]`,`G` |-> `FEMPTY`,`tn` |-> `entry_taint`]
    (SPEC_ALL grouped_selected_default_initializer_start)) >>
  disch_then (qx_choosel_then [`vars`,`alloc_start`,`alloc_end`,`checks`,`si`,`cut`,`last`,
    `dispatch_end`,`shadow_si`,`shadow_cut`,`v`,`Gv`,`tnv`,`t`,`J`,`tz`]
    (map_every assume_tac o CONJUNCTS)) >>
  drule_all row22_common_interval >>
  disch_then (qx_choosel_then [`entry`,`ce`,`registered`] (map_every assume_tac o CONJUNCTS)) >>
  `ci_mono cut sd` by
    (`ci_mono cut last` by metis_tac[ci_mono_emit_inst, SND] >>
     metis_tac[ci_mono_trans]) >>
  `ci_mono cut entry` by metis_tac[ci_mono_trans] >>
  qpat_assum `source_typing_ok _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_typing_ok_def]) >>
  `EXISTS external_has_defaults (FST (classify_functions tops))` by simp[] >>
  drule_all row22_dispatch_layout_bounds >> strip_tac >>
  drule_all (BETA_RULE row22_selected_initializer_syntax) >> strip_tac >>
  `cs_extends checks si` by
    (mp_tac (Q.INST [`st` |-> `checks`, `payable` |-> `common.ec_payable`,
      `mincd` |-> `min_calldata_size common.ec_env prefix 0`] compile_entry_checks_ci_mono) >>
     simp[ci_mono_def]) >>
  `sd.cs_next_id <= entry.cs_next_id /\ sd.cs_next_var <= entry.cs_next_var` by fs[ci_mono_def] >>
  Q.SUBGOAL_THEN `^row22_cut_facts u.cu_context fn cut t entry`
    (strip_assume_tac o SIMP_RULE bool_ss [MEM] o BETA_RULE)
  >- (BETA_TAC >> drule_all (BETA_RULE row22_before_cut_certificate_count) >>
      disch_then ACCEPT_TAC) >>
  qexistsl_tac [`fn`,`model`,`shadow_fn`,`common`,`entries`,`all_tvs`,
    `vars`,`alloc_start`,`alloc_end`,`checks`,`si`,`cut`,`last`,`dispatch_end`,`shadow_si`,`shadow_cut`,
    `v`,`Gv`,`tnv`,`t`,`J`,`tz`,`entry`,`ce`,`registered`] >>
  qunabbrev_tac `pk` >>
  `off = SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH defaults) all_tvs)) + 4` by decide_tac >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `specs = MAP _ _` SUBST_ALL_TAC >>
  qpat_x_assum `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>`
    SUBST_ALL_TAC >>
  rule_assum_tac (SIMP_RULE bool_ss [venom_state_accfupds, AC ADD_ASSOC ADD_COMM] o BETA_RULE) >>
  simp_tac bool_ss [venom_state_accfupds, AC ADD_ASSOC ADD_COMM] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
QED

Resume row22_selected_start_with_cut[nonpayable]:
  `~common.ec_payable /\ start.vs_call_ctx.cc_callvalue <> 0w` by metis_tac[] >>
  qpat_assum `start.vs_call_ctx = vs.vs_call_ctx`
    (fn eq => qpat_assum `FIND _ entries = SOME _` (assume_tac o PURE_REWRITE_RULE [GSYM eq])) >>
  qpat_assum `start.vs_call_ctx = vs.vs_call_ctx`
    (fn eq => qpat_assum `EVERY _ pre` (assume_tac o PURE_REWRITE_RULE [GSYM eq])) >>
  drule_all row22_nonpayable_origin >>
  disch_then (qx_choosel_then [`z`,`H`,`tn`] (map_every assume_tac o CONJUNCTS)) >>
  disj1_tac >> qexistsl_tac [`fn`,`z`,`H`,`tn`] >>
  qpat_assum `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>`
    (SUBST1_TAC o SYM) >> asm_rewrite_tac[]
QED

Finalise row22_selected_start_with_cut
