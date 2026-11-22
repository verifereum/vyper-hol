(* Carry allocation resources through the cut to the rejecting positional decoder. *)
Theory groupedRejectCutRegistration
Ancestors
  vyperLoweringCorrect ptrDiscipline acceptedContextPhi compileVyper fragGasOriginPtr list
  fragExec fragGasPath fragGasPathPtr pred_set venomInst venomState o1PassContract
  groupedDefaultArguments groupedEntryCommon groupedEntryResources callRejectMemory[ignore_grammar]
  registrationRejectMetadata groupedKeywordDecode bodyMemBopRestWordPath
  decoderOriginAllocationFrame deployBodyReachability contextRawReachable contextCodegenRel
  contextCodegenRelProps venomMemDefs exprLoweringProps allocaFrontierBound
  selectedAcceptedFold abiDecoderCoherence compileEnv vyperContext vyperTypeABI vyperABIEntries
  vyperCompiler allocaHistory entryRejectCode emitHelperProps fragGasOriginPtrLoop fragFuel
  loweringStateRelDefs allocaBudgetProps finite_map rich_list words pair
  arithmetic relation vyperAST allocasBelowFmpUpdatesProps groupedRejectCutAllocationProps

val _ = Parse.hide "tops";

(* Positional registration after the checked first initializer cut. *)
Triviality row22_grouped_defaults_metadata:
  lower_vyper_runtime_unit ts rp = SOME unit /\
  supported_program ts /\ source_typing_ok ts am tx /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions ts)) /\
  package_external_group ts rp.rpol_target tr nkeys
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off ==>
  ALL_DISTINCT (MAP FST args) /\
  ?tvs. OPT_MMAP (evaluate_type (type_env ts)) (MAP SND args) = SOME tvs /\
    LIST_REL (\(n,ty) tv.
      abi_decoder_coherent common.ec_env (type_env ts) common.ec_env.ce_struct_fields ty tv /\
      (?loc. FLOOKUP common.ec_env.ce_vars n = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args tvs
Proof
  strip_tac >>
  Cases_on `set_external_package_target rp.rpol_target
    (package_external_fn ts tr nkeys (mut,nr,rr,name,args,[],ret,stmts))` >>
  PairCases_on `r` >>
  drule_all registration_reject_classified_defaults_metadata >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `tvs` strip_assume_tac))) >>
  `common.ec_env = r0` by
    (qpat_x_assum `package_external_group _ _ _ _ _ = _` mp_tac >>
     simp[package_external_group_def, LET_THM] >>
     Cases_on `defaults = []` >> gvs[NULL_EQ] >>
     Cases_on `ret = NoneT` >>
     gvs[package_external_fn_def, set_external_package_target_def, LET_THM] >>
     strip_tac >> gvs[]) >>
  simp[] >> drule OPT_MMAP_LENGTH >> simp[] >> strip_tac >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >> qx_gen_tac `j` >> strip_tac >>
  qpat_x_assum `!n. n < LENGTH args ==> _` (qspec_then `j` mp_tac) >>
  simp[EL_ZIP, EL_MAP] >> Cases_on `EL j args` >> simp[]
QED

Triviality row22_positional_registration_inputs:
  lower_vyper_runtime_unit ts rp = SOME unit /\
  supported_program ts /\ source_typing_ok ts am tx /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions ts)) /\
  package_external_group ts rp.rpol_target tr nkeys
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off /\
  compile_create_kwarg_allocas common.ec_env specs alloc_start = (vars,alloc_end) /\
  compile_register_positional_args (compile_register_kwarg_vars common.ec_env vars)
    common.ec_pos_args 4 entry = (cef,registered) /\
  MEM (prefix,k) (abi_entries args defaults) /\
  OPT_MMAP (evaluate_type (type_env ts)) (MAP SND prefix) = SOME tvs /\
  LENGTH defaults <= LENGTH args /\ n = LENGTH args - LENGTH defaults ==>
  ALL_DISTINCT (MAP FST (TAKE n args)) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent (compile_register_kwarg_vars common.ec_env vars) (type_env ts)
      (compile_register_kwarg_vars common.ec_env vars).ce_struct_fields ty tv /\
    (?loc. FLOOKUP (compile_register_kwarg_vars common.ec_env vars).ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) (TAKE n args) (TAKE n tvs) /\
  compile_register_positional_args (compile_register_kwarg_vars common.ec_env vars)
    (build_positional_args (compile_register_kwarg_vars common.ec_env vars) (TAKE n args))
    4 entry = (cef,registered)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all row22_grouped_defaults_metadata >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `full_tvs` strip_assume_tac)) >>
  `defaults <> []` by
    (strip_tac >> qpat_x_assum `package_external_group _ _ _ _ _ = _` mp_tac >>
     simp[package_external_group_def, LET_THM, NULL_EQ]) >>
  `common.ec_pos_args = build_positional_args common.ec_env (TAKE n args) /\
   specs = MAP (\((name,ty),e). (name,ty,e)) (ZIP (DROP n args,defaults))` by
    (qpat_x_assum `package_external_group _ _ _ _ _ = _` mp_tac >>
     simp[package_external_group_def, LET_THM, NULL_EQ] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  `MAP (\(name,_,_,_). name) vars = MAP FST (DROP n args)` by
    (drule compile_create_kwarg_allocas_preserves_specs >> strip_tac >>
     qpat_assum `n = _` SUBST1_TAC >>
     irule grouped_kwarg_names >> simp[] >> qexists_tac `specs` >> simp[]) >>
  drule_all registered_kwarg_positional_metadata >> strip_tac >>
  `TAKE n tvs = TAKE n full_tvs` by
    (qpat_assum `MEM (prefix,k) _` (strip_assume_tac o REWRITE_RULE [abi_entries_member]) >>
     `tvs = TAKE (n + k) full_tvs` by
       (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME full_tvs`
          (qspec_then `n + k` mp_tac o MATCH_MP opt_mmap_take_some) >>
        fs[MAP_TAKE]) >>
     qpat_x_assum `tvs = TAKE _ full_tvs` SUBST1_TAC >>
     irule TAKE_TAKE_T >> decide_tac) >>
  qpat_x_assum `n = _` SUBST_ALL_TAC >> fs[]
QED

Theorem row22_real_cut_empty_oracle_no_wrap:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
      FEMPTY,entry_taint) marks (OK cut,G,tn) ==>
  !callee inst s. frag_reachable unit.cu_context fn (cut with vs_outcomes := []) callee inst s ==>
    dalloca_no_wrap inst s
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`prefix` |-> `[]`, `tail` |-> `cut.vs_outcomes`, `u` |-> `unit`]
    grouped_reject_cut_fragment_no_wrap) >>
  simp[] >> metis_tac[]
QED

Theorem row22_real_cut_empty_oracle_headroom:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
      FEMPTY,entry_taint) marks (OK cut,G,tn) ==>
  !callee inst s. frag_reachable unit.cu_context fn (cut with vs_outcomes := []) callee inst s ==>
    dalloca_fmp_headroom inst s
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`prefix` |-> `[]`, `tail` |-> `cut.vs_outcomes`, `u` |-> `unit`]
    grouped_reject_cut_fragment_no_dalloca) >>
  simp[dalloca_fmp_headroom_def] >> metis_tac[]
QED

Triviality row22_reject_cut_fmp:
  lower_vyper_runtime_unit ts rp = SOME unit /\
  supported_program ts /\ source_typing_ok ts am tx /\ source_deployment_rel ts am tx /\
  initial_venom_state_rel ts am tx vs /\ calldata_dispatch ts vs.vs_call_ctx.cc_calldata = NONE /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  ~s.vs_halted /\ gas_path unit.cu_context fn s n (OK w) /\ active_inst fn inst w /\
  (ctx_has_dalloca unit.cu_context ==>
    vs.vs_fmp = vs.vs_initial_fmp /\ unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) ==>
  (ctx_has_dalloca unit.cu_context ==> w2n w.vs_initial_fmp <= w2n w.vs_fmp)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> strip_tac >>
  drule_all raw_reachable_from_entry_path >> strip_tac >>
  qpat_assum `ctx_has_dalloca _ ==> _` (drule_then strip_assume_tac) >>
  `raw_variant vs.vs_initial_fmp vs vs` by
    simp[raw_variant_def, gas_variant_def, venom_state_component_equality] >>
  drule_all call_reject_raw_variant_no_wrap >> metis_tac[]
QED

Triviality row22_cut_resources:
  lower_vyper_runtime_unit ts rp = SOME unit /\
  supported_program ts /\ source_typing_ok ts am tx /\ source_deployment_rel ts am tx /\
  initial_venom_state_rel ts am tx vs /\ calldata_dispatch ts vs.vs_call_ctx.cc_calldata = NONE /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
    (s,FEMPTY,entry_taint) tags (OK w,H,tn) /\ active_inst fn inst w /\
  (ctx_has_dalloca unit.cu_context ==>
    vs.vs_fmp = vs.vs_initial_fmp /\ unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) ==>
  fn_inst_ids_distinct fn /\ unit_alloca_budget unit.cu_context < dimword (:256) /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256) /\
  ~w.vs_halted /\ alloca_inv w /\ alloca_frontier_inv unit.cu_context fn site w /\
  (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp w /\
    w.vs_alloca_next + pending_alloca_size fn w <= w2n w.vs_initial_fmp)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp` by metis_tac[] >>
  `((initial_compile_state "__entry").cs_current_bb = "__entry") /\
    (initial_compile_state "__entry").cs_current_insts = []` by
    simp[initial_compile_state_def] >>
  drule_all grouped_dispatch_initial_resources >>
  disch_then (qspec_then `site` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_path_ptr_erase >> strip_tac >>
  drule gas_path_normal >> strip_tac >>
  `alloca_history fn s` by (irule alloca_history_empty >> simp[]) >>
  `alloca_inv w` by (drule rest_word_path_alloca >> simp[]) >>
  drule_all decoder_origin_path_allocation_frame >> strip_tac >>
  `alloca_frontier_inv unit.cu_context fn site w` by
    (irule alloca_frontier_charge_frame >> qexists_tac `s` >> asm_rewrite_tac[]) >>
  `unit.cu_context.ctx_entry = SOME "__entry" /\ fn_entry_label fn = SOME "__entry"` by
    metis_tac[lower_vyper_runtime_unit_context_entry,
      entryRejectCodeTheory.lower_vyper_runtime_unit_entry_label] >>
  `LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)` by
    (qpat_x_assum `LENGTH s.vs_call_ctx.cc_calldata < _` mp_tac >> simp[]) >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `w2n w.vs_initial_fmp <= w2n w.vs_fmp` by
    (drule_all row22_reject_cut_fmp >> simp[]) >>
  qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp s /\ _` (drule_then strip_assume_tac) >>
  qpat_x_assum `s = _` kall_tac >>
  `w.vs_alloca_next + pending_alloca_size fn w <= w2n w.vs_initial_fmp` by asm_rewrite_tac[] >>
  `w.vs_alloca_next <= w2n w.vs_initial_fmp` by decide_tac >>
  simp[allocas_below_fmp_from_frontier]
QED

Triviality row22_cut_jump_active:
  emit_inst JMP [Label entry.cs_current_bb] [] cut = ((),last) /\
  fn_has_code cut last fn /\ at_point cut w ==>
  active_inst fn (mk_inst cut.cs_next_id JMP [Label entry.cs_current_bb] []) w
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qpat_assum `!i. i < _ ==> _` (qspec_then `0` mp_tac) >>
  fs[at_point_def] >>
  metis_tac[contextCodegenRelPropsTheory.lookup_instruction_active]
QED

Triviality row22_cut_jump_registration:
  emit_inst JMP [Label entry.cs_current_bb] [] cut = ((),last) /\
  fn_has_code cut last fn /\ at_point cut w /\ entry.cs_current_insts = [] /\
  fn_has_code entry registered fn /\ fn_inst_ids_distinct fn /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  compile_register_positional_args ce (build_positional_args ce args) 4 entry = (cef,registered) /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH w.vs_call_ctx.cc_calldata /\
  LENGTH w.vs_call_ctx.cc_calldata < dimword (:256) /\
  calldata_decode_args w.vs_call_ctx.cc_calldata tvs 0 = NONE /\
  unit_alloca_budget ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w /\
    w.vs_alloca_next + pending_alloca_size fn w <= w2n w.vs_initial_fmp) /\
  alloca_inv w /\ alloca_frontier_inv ctx fn site w /\
  (!id e. FLOOKUP w.vs_allocas id = SOME e ==> id < entry.cs_next_id) /\
  fresh_vars_wrt entry w /\ ~w.vs_halted ==>
  ?z J tz. z.vs_returndata = [] /\
    !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (w,H,tn) [] (Abort Revert_abort z,J,tz)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `allocas_from 0 w /\ (ctx_has_dalloca ctx ==> allocas_below_fmp w)` by
    (simp[allocas_from_def] >> metis_tac[]) >>
  drule_all grouped_entry_jump_to_common >>
  disch_then (qspecl_then [`tn`,`[]`,`H`] strip_assume_tac) >>
  qabbrev_tac `landed = jump_to entry.cs_current_bb w` >>
  `(alloca_inv landed <=> alloca_inv w) /\
    (alloca_frontier_inv ctx fn site landed <=> alloca_frontier_inv ctx fn site w)` by
    (irule calldataDynOwnedTheory.calldata_alloca_invariants_fields >>
     simp[Abbr `landed`, jump_to_def]) >>
  `allocas_below_fmp landed <=> allocas_below_fmp w` by
    (irule allocas_below_fmp_fields >> simp[Abbr `landed`, jump_to_def]) >>
  `alloca_inv landed /\ alloca_frontier_inv ctx fn site landed /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp landed /\
     landed.vs_alloca_next + pending_alloca_size fn landed <= w2n landed.vs_initial_fmp) /\
   (!id e. FLOOKUP landed.vs_allocas id = SOME e ==> id < entry.cs_next_id) /\
   fresh_vars_wrt entry landed /\ ~landed.vs_halted /\ landed.vs_call_ctx = w.vs_call_ctx` by
    (fs[Abbr `landed`, jump_to_def, lookup_var_def, fresh_vars_wrt_def, pending_alloca_size_def] >>
     metis_tac[]) >>
  qpat_assum `at_point entry landed` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  drule_at (Pat `alloca_frontier_inv _ _ _ landed`) coherent_registration_reject_path >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`tvs`,`tn`,`env`,`H`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`z`,`J`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`J`,`tz`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`H`,`landed`,`tn`] >> simp[]
QED

Theorem row22_cut_registration_abort:
  lower_vyper_runtime_unit ts rp = SOME unit /\
  supported_program ts /\ source_typing_ok ts am tx /\ source_deployment_rel ts am tx /\
  initial_venom_state_rel ts am tx vs /\ calldata_dispatch ts vs.vs_call_ctx.cc_calldata = NONE /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  (ctx_has_dalloca unit.cu_context ==>
    vs.vs_fmp = vs.vs_initial_fmp /\ unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,FEMPTY,entry_taint)
    tags (OK w,H,tn) /\
  at_point cut w /\ w.vs_call_ctx = vs.vs_call_ctx /\
  fresh_vars_wrt entry w /\ (!id e. FLOOKUP w.vs_allocas id = SOME e ==> id < entry.cs_next_id) /\
  emit_inst JMP [Label entry.cs_current_bb] [] cut = ((),last) /\
  fn_has_code cut last fn /\ entry.cs_current_insts = [] /\ fn_has_code entry registered fn /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions ts)) /\
  package_external_group ts rp.rpol_target tr nkeys
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off /\
  compile_create_kwarg_allocas common.ec_env specs alloc_start = (vars,alloc_end) /\
  compile_register_positional_args (compile_register_kwarg_vars common.ec_env vars)
    common.ec_pos_args 4 entry = (cef,registered) /\
  MEM (prefix,k) (abi_entries args defaults) /\
  OPT_MMAP (evaluate_type (type_env ts)) (MAP SND prefix) = SOME tvs /\
  LENGTH defaults <= LENGTH args /\ n = LENGTH args - LENGTH defaults /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
  calldata_decode_args vs.vs_call_ctx.cc_calldata (TAKE n tvs) 0 = NONE ==>
  ?z J tz. z.vs_returndata = [] /\
    !D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[]) (w,H,tn) [] (Abort Revert_abort z,J,tz)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all row22_cut_jump_active >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST
    [`s` |-> `vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>`]
    row22_cut_resources)) >> disch_then (qspec_then `ARB:instruction` strip_assume_tac) >>
  drule_all row22_positional_registration_inputs >> strip_tac >>
  `4 + SUM (MAP tv_abi_size (TAKE n tvs)) <= LENGTH w.vs_call_ctx.cc_calldata` by
    (qspecl_then [`n`,`tvs`] mp_tac prefix_head_size_le >>
     qpat_x_assum `w.vs_call_ctx = _` SUBST1_TAC >> decide_tac) >>
  drule_at (Pat `alloca_frontier_inv _ _ _ w`) row22_cut_jump_registration >>
  disch_then (drule_at (Pat `emit_inst JMP _ _ cut = _`)) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ (build_positional_args _ _) _ _ = _`)) >>
  disch_then (qspecl_then [`TAKE n tvs`,`tn`,`type_env ts`,`H`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
  disch_then ACCEPT_TAC
QED
