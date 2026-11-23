Theory groupedFallbackCallRoute
Ancestors
  groupedRuntimeBodyCode groupedDispatchPath groupedEntryPackage groupedEntryExit
  groupedRuntimeEndpoint groupedEntryResources fallbackEntryEndpoint runtimeFallbackPackageEnvironment
  entryRejectAllocationIds entryValueRejectFacts sourceValueRejection
  externalEntryBound externalBodySupport
  defaultDispatchFacts entryDispatchProps vyperCalldata vyperTypeContractContext vyperTypeContract
  vyperTypeBindArguments entryStateRel vyperInterpreter vyperState
  compileVyper moduleLowering compileEnv emitHelper e2eDefs
  calldataSelectorProps selectedAcceptedFold bodyPtrDefs fragExec
  gasShadowRuntimeOps gasShadowModuleDefs gasShadowState gasShadowUnit
  fragGasOriginPtr gasSummary vyperStorageFootprint ptrDiscipline
  vyperLoweringCorrect loweringStateRelDefs venomInst venomState
  loweringPosts exprLoweringProps allocaFrontierRoom entryReachBodyFmp
  selectedEntryPrefixCode decoderOriginAllocationFrame fragFuel entryCompileIntervals
  groupedValueRejectSite entryCreateGroupedLayout list pair finite_map words

val _ = Parse.hide "body";

Theorem grouped_fallback_source_parameters[local]:
  source_typing_ok tops am tx /\
  calldata_dispatch tops cd = SOME (tx.function_name,tx.args) /\
  (LENGTH cd < 4 \/
   FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
     (abi_external_signatures tops) = NONE) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,ds,ret,fbody) ==>
  tx.function_name = "__default__" /\ tx.args = [] /\ args = [] /\ ds = [] /\
  EXISTS is_default_decl tops
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule default_dispatch_raw_cases >>
  disch_then (DISJ_CASES_THEN2
    (CONJUNCTS_THEN2 (K ALL_TAC) strip_assume_tac) strip_assume_tac)
  >- (qpat_assum `EXISTS is_default_decl tops` mp_tac >> pure_rewrite_tac[EXISTS_MEM] >>
      disch_then (qx_choose_then `d` strip_assume_tac) >>
      Cases_on `d` >> fs[is_default_decl_def] >>
      rename1 `MEM (FunctionDecl vis _ _ _ _ _ _ _ _) tops` >>
      Cases_on `vis` >> gvs[is_default_decl_def] >>
      `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
        metis_tac[source_typing_ok_external_names_distinct] >>
      rename1 `MEM (FunctionDecl External m n rr "__default__" pa df rt fb) tops` >>
      `vyperInterpreter$lookup_function NONE "__default__" External tops =
        SOME (m,n,pa,df,rt,fb)` by
        (irule lookup_function_external_unique_decl >> simp[] >>
         qexists_tac `FunctionDecl External m n rr "__default__" pa df rt fb` >>
         simp[external_name_keys_toplevel_def, vyperInterpreterTheory.lookup_function_def]) >>
      `function_header_ok External m n rr "__default__" pa df rt` by
        metis_tac[nonreentrantEntryEquivTheory.source_typing_function_header] >>
      `pa = []` by metis_tac[supportedNamesTheory.supported_fallback_no_arguments] >>
      `LENGTH df <= LENGTH pa` by
        (qpat_assum `source_typing_ok _ _ _`
           (strip_assume_tac o REWRITE_RULE [source_typing_ok_def]) >>
         drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
         `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
            External m n pa df rt fb` by
           (irule check_contract_runtime_function_body_MEM >> simp[] >>
            qexistsl_tac [`"__default__"`,`rr`] >> fs[]) >>
         gvs[check_function_body_def, LET_THM]) >>
      gvs[] >> metis_tac[EXISTS_MEM]) >>
  fs[] >> decide_tac
QED

Theorem grouped_fallback_miss_widths[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  source_typing_ok tops am tx /\
  classify_functions tops = (exts,ints,fb,ctor) /\
  groups = MAP (package_external_group tops target trans keys) exts /\
  (LENGTH cd < 4 \/
   FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
     (abi_external_signatures tops) = NONE) ==>
  (4 <= LENGTH cd ==>
   EVERY (\group. case group of
     ExternalSingle (sel,lbl,tz) pkg => calldata_method_id cd <> n2w sel
   | ExternalDefaults common entries specs _ =>
       FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) entries = NONE /\
       EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
     groups)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  `EVERY (\group. case group of
     ExternalSingle (sel,_,_) _ => calldata_method_id cd <> n2w sel
   | ExternalDefaults _ entries _ _ =>
       FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) entries = NONE) groups` by
    (irule grouped_selector_from_source_miss >> simp[] >>
     qexistsl_tac [`keys`,`target`,`tops`,`trans`] >>
     Cases_on `LENGTH cd < 4` >> fs[] >> decide_tac) >>
  `EVERY (\group. case group of ExternalSingle _ _ => T
   | ExternalDefaults common entries specs _ =>
       EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
     groups` by
    (qpat_x_assum `groups = _` SUBST1_TAC >>
     qpat_assum `source_typing_ok _ _ _`
       (strip_assume_tac o REWRITE_RULE [source_typing_ok_def]) >>
     drule_all checked_grouped_package_keyword_widths >> simp[]) >>
  qpat_x_assum `EVERY _ groups` (assume_tac o REWRITE_RULE [EVERY_MEM]) >>
  qpat_x_assum `EVERY _ groups` (assume_tac o REWRITE_RULE [EVERY_MEM]) >>
  pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `grp` >> strip_tac >>
  qpat_x_assum `!e. MEM e groups ==> _` (drule_then mp_tac) >>
  qpat_x_assum `!e. MEM e groups ==> _` (drule_then mp_tac) >>
  Cases_on `grp`
  >- (rename1 `MEM (ExternalSingle selector package) groups` >>
      PairCases_on `selector` >> simp[]) >>
  simp[]
QED

(* Use the passing-checks interface with an empty check interval to reach
   the actual fallback guard, without assuming that guard passes. *)
Theorem grouped_fallback_reach_guard[local]:
  compile_group_dispatch_linear groups fallback start = (jobs,dispatch_end) /\
  fn_has_code start dispatch_end fn /\ EVERY group_entry_labels_ok groups /\
  ci_mono dispatch_end checks /\ checks.cs_current_bb = fallback /\
  checks.cs_current_insts = [] /\ lookup_block fallback fn.fn_blocks = SOME target /\
  (4 <= LENGTH s.vs_call_ctx.cc_calldata ==>
    EVERY (\group. case group of
      ExternalSingle (sel,lbl,tz) pkg =>
        calldata_method_id s.vs_call_ctx.cc_calldata <> n2w sel
    | ExternalDefaults common entries specs _ =>
        FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel)
          entries = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
      groups) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  selected_registration_resources ctx fn site lo start s /\ s.vs_allocas = FEMPTY /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?t J tz.
    selected_registration_resources ctx fn site lo checks t /\
    selected_registration_frame s tn t tz /\ t.vs_memory = s.vs_memory /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
     t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,J,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_entry_checks 4 T checks = ((),checks)` by
    simp[compile_entry_checks_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  `fn_has_code checks checks fn` by
    (simp[fn_has_code_def, emitted_blocks_def] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`pay` |-> `T`]
    grouped_fallback_checks_pass)) >>
  simp_tac bool_ss [] >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] ACCEPT_TAC)
QED

(* Empty source scope and compiler locals, but not necessarily empty ALLOCAs:
   the missed grouped selectors may already have allocated keywords. *)
Theorem grouped_fallback_empty_body_state[local]:
  initial_venom_state_rel tops am tx vs /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  send_call_value mut cx (initial_state am [FEMPTY] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es) /\
  selected_registration_frame vs entry_taint t tn /\
  selected_registration_resources ctx fn site 0 st t /\
  t.vs_initial_fmp = vs.vs_initial_fmp /\
  (ctx_has_dalloca ctx ==> unit_alloca_budget ctx <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  unit_alloca_budget ctx < dimword (:256) /\
  ce.ce_vars = FEMPTY /\ ce.ce_module = NONE /\ ~ce.ce_is_ctor /\
  ce.ce_imm_alloca = NONE /\ ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  immutable_section_layout ce tops /\ storage_vars_rel ce cx /\ transient_vars_rel ce cx ==>
  return_buf_frame NONE ce st t /\
  (!H:(bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (cx_dead H cx) 0 NONE ce cx es G tn t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  `es.scopes = [FEMPTY]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  `local_ptrs_rel fn ce [FEMPTY] t` by simp[local_ptrs_rel_def, local_region_def] >>
  qpat_assum `selected_registration_frame _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
    state_rel H fn ce (initial_evaluation_context am.sources am.layouts tx NONE) es t` by
    (gen_tac >> irule body_entry_state_rel_runtime >> simp[initial_evaluation_context_def] >>
     qexistsl_tac [`am`,`FEMPTY`,`mut`,`tops`,`vs`] >> fs[initial_evaluation_context_def]) >>
  qpat_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  `alloca_room ctx fn t` by metis_tac[registration_frontier_alloca_room] >>
  `fmp_room ctx fn t` by
    (irule entry_frontier_fmp_room >> fs[initial_venom_state_rel_def] >>
     goal_assum (drule_at Any)) >>
  simp[return_buf_frame_def, ghost_inv_at_def, return_buf_ptr_def,
       stor_taint_ok_at_def, stmt_state_rel_def, immutable_alloca_sep_def,
       immutable_decl_sep_def, immutable_base_zero_def, entry_taint_def,
       allocas_from_def] >> metis_tac[]
QED

Theorem grouped_fallback_call_route_with_reject_site:
  lower_vyper_runtime_unit tops rp = SOME unit /\ supported_program tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name,tx.args) /\
  (LENGTH vs.vs_call_ctx.cc_calldata < 4 \/
   FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector vs.vs_call_ctx.cc_calldata)
     (abi_external_signatures tops) = NONE) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,ds,ret,fbody) ==>
  (?es. runtime_body_endpoint tops rp unit am tx vs es mut nr args ds ret
          (subst_consts_stmts (module_consts_env tops []) fbody)) \/
  (grouped_value_reject_site unit vs /\
   ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
              tops ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail. FST (call_external (SOME vs.vs_outcomes)
                    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
            INR (Error (RuntimeError "msg.gas: no gas reading"))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_fallback_source_parameters >> strip_tac >>
  `vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,[],[],ret,fbody)` by fs[] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >>
  `EXISTS external_has_defaults exts` by fs[] >>
  drule_all lower_grouped_runtime_pair >> strip_tac >>
  drule_all default_fallback_classified >> simp[] >> strip_tac >>
  qabbrev_tac `stmts = subst_consts_stmts (module_consts_env tops []) fbody` >>
  qabbrev_tac `rt = if ret = NoneT then NONE else SOME ret` >>
  `?ce. fall = SOME (ce,mut = Payable,nr,global_nonreentrant_slot,T,mut = View,stmts,rt)` by
    simp[package_fallback_fn_def, set_fallback_package_target_def, Abbr `stmts`, Abbr `rt`] >>
  pop_assum strip_assume_tac >>
  drule_all grouped_shadow_entry_dispatch_with_layout >>
  disch_then (qx_choosel_then [`shadow_installed`,`shadow_fn`,`sf`,`fallback`,`jobs`,
    `sd`,`shd`,`sx`,`shx`,`sn`,`shn`,`se`,`she`] (map_every assume_tac o CONJUNCTS)) >>
  `shadow_installed = shadow_unit` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `shadow_installed = _` SUBST_ALL_TAC >>
  qabbrev_tac `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `?site. selected_registration_resources unit.cu_context fn site 0 sf s /\
    s.vs_allocas = FEMPTY /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    fn_inst_ids_distinct fn /\ unit_alloca_budget unit.cu_context < dimword (:256) /\
    (!name bb. lookup_block name fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
    (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp s /\
     s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp)` by
    (qexists_tac `ARB` >> irule grouped_dispatch_initial_resources >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[Abbr `s`] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  suspend "guard"
QED

Resume grouped_fallback_call_route_with_reject_site[guard]:
  `compile_fallback_body ce (mut = Payable) nr global_nonreentrant_slot T
    (mut = View) stmts rt sn = ((),se) /\
   compile_fallback_body (gas_shadow_env T ce) (mut = Payable) nr global_nonreentrant_slot T
    (mut = View) (MAP gas_shadow_stmt stmts) rt shn = ((),she)` by
    (qpat_assum `(case fall of NONE => _ | SOME (_,_,_,_,_,_,_,_) => _) sn = _` mp_tac >>
     qpat_assum `(case OPTION_MAP gas_shadow_fallback_package fall of NONE => _
       | SOME (_,_,_,_,_,_,_,_) => _) shn = _` mp_tac >>
     qpat_assum `fall = SOME (_,_,_,_,_,_,_,_)` SUBST1_TAC >>
     simp[gas_shadow_fallback_package_def]) >>
  `ci_mono sd sn` by
    (`ci_mono sd sx` by metis_tac[compile_external_jobs_ci_mono, SND] >>
     `ci_mono sx sn` by metis_tac[ci_mono_new_block, SND] >>
     metis_tac[ci_mono_trans]) >>
  `?target. lookup_block fallback fn.fn_blocks = SOME target` by
    (`cs_extends sn se` by metis_tac[cs_appends_def, cs_appends_fallback_body] >>
     drule_all fn_has_code_start >> simp[]) >>
  pop_assum strip_assume_tac >>
  `4 <= LENGTH s.vs_call_ctx.cc_calldata ==>
    EVERY (\group. case group of
      ExternalSingle (sel,lbl,tz) pkg =>
        calldata_method_id s.vs_call_ctx.cc_calldata <> n2w sel
    | ExternalDefaults common entries specs _ =>
        FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel)
          entries = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
      groups` by
    (simp_tac (srw_ss()) [Abbr `s`] >> strip_tac >>
     drule_all grouped_fallback_miss_widths >> simp_tac bool_ss []) >>
  drule_all grouped_fallback_reach_guard >>
  disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
    (qx_choosel_then [`t`,`G`,`tn`] (map_every assume_tac o CONJUNCTS))) >>
  drule_all grouped_fallback_guarded_code >>
  disch_then (qx_choose_then `sha` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `compile_fallback_body _ _ _ _ _ _ (MAP gas_shadow_stmt _) _ _ = _` kall_tac >>
  drule_all grouped_fallback_guarded_code >>
  disch_then (qx_choose_then `sa` (map_every assume_tac o CONJUNCTS)) >>
  `cs_extends sa se /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se))` by
    (irule selected_grouped_body_layout_at >> conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexists_tac `se` >> simp[cs_extends_refl]) >>
  `gas_shadow_state sa sha` by
    (mp_tac (Q.INST [`min_cds` |-> `4`, `payable` |-> `mut = Payable`]
       gas_shadow_compiles_compile_entry_checks) >>
     simp_tac bool_ss [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sn`,`shn`] mp_tac) >> asm_rewrite_tac[SND]) >>
  suspend "value"
QED

Resume grouped_fallback_call_route_with_reject_site[value]:
  `gas_shadow_context unit.cu_context shadow_unit.cu_context /\
   MEM fn unit.cu_context.ctx_functions /\ MEM shadow_fn shadow_unit.cu_context.ctx_functions /\
   phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[gas_shadow_unit_def, venomInstTheory.lookup_function_MEM] >>
  `t.vs_call_ctx.cc_callvalue = n2w tx.value` by
    fs[selected_registration_frame_def, Abbr `s`, initial_venom_state_rel_def,
       venom_env_rel_def, call_ctx_rel_def] >>
  `tx.value < dimword (:256)` by
    fs[source_typing_ok_def, vyperTypeContractSoundnessTheory.call_tx_well_typed_def, dimword_def] >>
  `~block_is_terminated sn` by simp[block_is_terminated_def] >>
  Cases_on `mut = Payable \/ tx.value = 0`
  >- suspend "accepted" >>
  suspend "rejected"
QED

Resume grouped_fallback_call_route_with_reject_site[accepted]:
  disj1_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `?es. send_call_value mut cx (initial_state am [FEMPTY] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es)` by
    (Cases_on `send_call_value mut cx (initial_state am [FEMPTY] with
       <|outcomes := SOME vs.vs_outcomes; requests := []|>)` >>
     rename1 `_ = (res,es)` >> Cases_on `res` >> simp[] >>
     `value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
     fs[Abbr `cx`] >> drule_all send_call_value_rejects_only_nonpayable >> simp[]) >>
  qexists_tac `es` >>
  `t.vs_call_ctx = vs.vs_call_ctx` by fs[selected_registration_frame_def, Abbr `s`] >>
  `LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by fs[Abbr `s`] >>
  `mut = Payable \/ t.vs_call_ctx.cc_callvalue = 0w` suffices_by
    (disch_then assume_tac >>
     qpat_x_assum `compile_entry_checks _ _ shn = _` kall_tac >>
     drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`m` |-> `4`]
       grouped_default_checks_pass_origin)) >>
     disch_then (qspecl_then [`tn`,`[]`,`G`]
       (qx_choosel_then [`u`,`J`,`tz`] (map_every assume_tac o CONJUNCTS))) >>
     suspend "body") >>
  fs[]
QED

Resume grouped_fallback_call_route_with_reject_site[body]:
  `selected_registration_frame vs entry_taint u tz` by
    fs[selected_registration_frame_def, Abbr `s`] >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
     (s,FEMPTY,entry_taint) [] (OK u,J,tz)` by
     (rpt gen_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ (OK t,G,tn)`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ (OK u,J,tz)`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `u.vs_initial_fmp = vs.vs_initial_fmp` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ (OK u,J,tz)`
      (qspecl_then [`ARB`,`{}`] assume_tac) >>
     drule_all decoder_origin_path_allocation_frame >> simp[Abbr `s`]) >>
  `cx = initial_evaluation_context am.sources am.layouts tx NONE` by simp[Abbr `cx`] >>
  qpat_assum `fb = SOME _` (fn fb_eq =>
    qpat_assum `fall = set_fallback_package_target _ _` (fn pkg_eq =>
      qpat_assum `fall = SOME _` (assume_tac o SUBS [fb_eq] o SUBS [pkg_eq]))) >>
  drule_all fallback_empty_environment >> strip_tac >>
  drule fallback_empty_source_external_package >> strip_tac >>
  `~block_is_terminated sa` by metis_tac[compile_entry_checks_open] >>
  `local_ptrs_reserved ce sa` by simp[local_ptrs_reserved_def] >>
  `at_point sa u /\ fresh_vars_wrt sa u` by
    fs[selected_registration_resources_def, at_point_def] >>
  `bind_arguments (type_env tops) [] tx.args = SOME FEMPTY` by simp[bind_arguments_def] >>
  `!gx. external_entry_bound tops am tx vs.vs_outcomes
        (gas_explicit [] vs.vs_gas_readings ++ gx) mut [] [] (es with gas_obs := gx)` by
    (qpat_assum `cx = _` (SUBST_ALL_TAC) >>
     drule_all external_entry_bound_no_defaults >> simp[gas_explicit_def]) >>
  `es.gas_obs = [] /\ es.storage_trace = []` by
    (drule external_send_call_value_frame >>
     simp[evaluation_state_component_equality, initial_state_def]) >>
  `storage_trace_domain cx (initial_state am []) es.storage_trace` by
    simp[storage_trace_domain_def, valid_horizon_def, storage_trace_horizon_def,
      storage_trace_regions_def, storage_trace_locks_def, storage_observations_ok_def,
      regions_consistent_def, storage_locks_separated_def, storage_well_formed_on_def,
      storage_roots_fit_def, storage_trace_backends_well_formed_def] >>
  `storage_vars_rel ce cx /\ transient_vars_rel ce cx` by simp[Abbr `cx`] >>
  drule_all grouped_fallback_empty_body_state >>
  disch_then (qspec_then `J` strip_assume_tac) >>
  `!D. gas_origin_ptr_path
      (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,unit.cu_context,fn,[])
      (s,FEMPTY,entry_taint) [] (OK u,J,tz)` by
    (rpt gen_tac >> first_x_assum irule) >>
  qunabbrev_tac `rt` >>
  irule (Q.INST [`marks` |-> `[]`, `ce0` |-> `ce`] grouped_registered_body_endpoint) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `fbody` >> simp[Abbr `stmts`]) >>
  qexistsl_tac [`J`,`bb`,`ce`,`cx`,`se`,`fn`,`mut = Payable`,`mut = View`,
    `"fn_" ++ "__default__"`,`4`,`global_nonreentrant_slot`,`[]`,
    `if ret = NoneT then NONE else SOME ret`,`s`,`sa`,`she`,`shadow_fn`,`sha`,`shadow_unit`,
    `u`,`tz`,`T`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[constSubstCorrectTheory.subst_consts_exprs_map] >>
  simp[GSYM compile_env_component_equality, Abbr `s`]
QED

Resume grouped_fallback_call_route_with_reject_site[rejected]:
  `mut <> Payable /\ tx.value <> 0` by fs[] >>
  `t.vs_call_ctx.cc_callvalue <> 0w` by
    simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD] >>
  `compile_entry_checks 4 F sn = ((),sa)` by fs[] >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) [] (OK t,G,tn)` by fs[Abbr `s`] >>
  qpat_assum `selected_registration_resources _ _ _ _ sn t`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  `LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH ds` by simp[] >>
  `(ctx_has_dalloca unit.cu_context ==> allocas_below_fmp t)` by simp[] >>
  `t.vs_inst_idx = 0` by fs[] >>
  `MEM shadow_fn shadow_unit.cu_context.ctx_functions` by simp[] >>
  qpat_x_assum `compile_entry_checks _ _ shn = _` kall_tac >>
  disj2_tac >> conj_tac
  >- (irule grouped_value_reject_site_at >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G`,`bb`,`sa`,`fn`,`4`,`sn`,`t`,`tn`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all grouped_entry_value_rejected >> strip_tac >>
  qexists_tac `[]` >> simp[gas_explicit_def]
QED

Finalise grouped_fallback_call_route_with_reject_site

Theorem grouped_fallback_call_route:
  lower_vyper_runtime_unit tops rp = SOME unit /\ supported_program tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name,tx.args) /\
  (LENGTH vs.vs_call_ctx.cc_calldata < 4 \/
   FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector vs.vs_call_ctx.cc_calldata)
     (abi_external_signatures tops) = NONE) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,ds,ret,fbody) ==>
  (?es. runtime_body_endpoint tops rp unit am tx vs es mut nr args ds ret
          (subst_consts_stmts (module_consts_env tops []) fbody)) \/
  (?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
              tops ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail. FST (call_external (SOME vs.vs_outcomes)
                    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
            INR (Error (RuntimeError "msg.gas: no gas reading"))))
Proof
  disch_then (mp_tac o MATCH_MP grouped_fallback_call_route_with_reject_site) >>
  strip_tac >> metis_tac[]
QED
