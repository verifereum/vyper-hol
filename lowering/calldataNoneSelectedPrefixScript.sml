(* Route a raw selector hit to the installed checks for that package. *)
Theory calldataNoneSelectedPrefix
Ancestors
  calldataNoneMetadata defaultDispatchPlacement defaultDispatchRouting
  entryPrefixPtr entryValueRevertPtr entryReachBodyFmp acceptedContextPhi
  vyperLoweringCorrect vyperCompiler venomInstIdsProps fragExec
  fragGasOriginPtr ptrDiscipline moduleLoweringProps emitHelperProps
  vyperCalldata vyperInterpreter vyperTypeContract vyperTypeContractContext
  e2eDefs supportedProgram checkedSelectorTableProps list
  venomInst venomWf compileEnv compileVyper constSubst dispatchedValueSelection
  entryDispatchProps entryCheckIntervals actualRegistrationCode loweringShapeProps
  loweringShapeDefs loweringShapeRules venomState venomExecSemantics venomExecProofs
  actualEntryAllocationFrame entryDispatchPtr finite_map moduleLowering words
  allocaFrontierBound exprLoweringProps[qualified,ignore_grammar]

Theorem none_selected_check_prefix:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts =
    cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
    SOME (name,tys) ==>
  ?mut nr rr args ret fbody tvs ce pos mincd pay key ut iv rt
    opened checked ce' last func t G tn.
    MEM (mut,nr,rr,name,args,([] : vyperAST$expr list),ret,fbody) (FST (classify_functions tops)) /\
    (?rawbody. vyperInterpreter$lookup_function NONE name External tops =
      SOME (mut,nr,args,[],ret,rawbody) /\
      fbody = subst_consts_stmts (module_consts_env tops []) rawbody) /\
    tys = MAP SND args /\
    OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K context$global_nonreentrant_slot)
        (mut,nr,rr,name,args,([] : vyperAST$expr list),ret,fbody)) =
      ("fn_" ++ name,ce,pos,mincd,pay,nr,key,ut,iv,fbody,rt) /\
    ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
    mincd = 4 + SUM (MAP tv_abi_size tvs) /\ mincd < dimword (:256) /\
    LIST_REL (\(argname,ty) (ty',tv). ty = ty' /\
      abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
      (?loc. FLOOKUP ce.ce_vars argname = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args (ZIP (tys,tvs)) /\
    compile_entry_checks mincd pay opened = ((),checked) /\
    compile_register_positional_args ce pos 4 checked = (ce',last) /\
    fn_has_code opened checked func /\ fn_has_code checked last func /\
    cs_extends opened checked /\ cs_extends checked last /\
    shape_state opened /\ shape_state checked /\ shape_state last /\
    opened.cs_current_bb = "fn_" ++ name /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\ fn_inst_ids_distinct func /\
    (?bb. lookup_block "__entry" func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
    entry_prov func
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>) FEMPTY = FEMPTY /\
    entry_taint_vars func
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>) entry_taint = entry_taint /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>,FEMPTY,entry_taint) [] (OK t,G,tn)) /\
    vars_pc_only vs t /\ fresh_vars_wrt opened t /\ ~t.vs_halted /\
    t.vs_current_bb = opened.cs_current_bb /\ t.vs_inst_idx = 0 /\
    t.vs_call_ctx = vs.vs_call_ctx /\
    LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\ allocas_from 0 t /\
    (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp t) /\
    tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {}
Proof
  strip_tac >> drule venomInstTheory.FIND_MEM >> strip_tac >>
  drule_all none_signature_evaluates >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    (fs[source_typing_ok_def] >>
     drule check_contract_external_names_distinct >> simp[contract_keys_def]) >>
  `?rawbody. vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,[],ret,rawbody) /\
    fbody = subst_consts_stmts (module_consts_env tops []) rawbody` by
    suspend "lookup" >>
  qpat_x_assum `fbody = subst_consts_stmts _ rawbody` (mk_asm "compiled_body") >>
  `ALL_DISTINCT (MAP FST
    (build_selectors (type_env tops) (FST (classify_functions tops))))` by
    (fs[source_typing_ok_def] >>
     drule (INST_TYPE [alpha |-> ``:160 word`` ]
       checkedSelectorTablePropsTheory.check_contract_selectors_distinct) >> simp[]) >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `venomInst$lookup_function "__entry" _ = SOME func` >>
  `?elbl. fn_entry_label func = SOME elbl` by
    (drule venomInstTheory.lookup_function_MEM >> strip_tac >>
     gvs[lowering_context_ok_def, EVERY_MEM] >>
     qpat_x_assum `!fn. MEM fn _ ==> ALL_DISTINCT _ /\ fn_has_entry fn` drule >>
     simp[fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
     Cases_on `func.fn_blocks` >> simp[]) >>
  `fn_inst_ids_distinct func` by
    (`ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
       metis_tac[venomInstTheory.lookup_function_MEM, ctx_inst_ids_distinct_fn,
                 lowering_context_ok_static_integrity] >>
     gvs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  drule_all default_runtime_compile_layout >> strip_tac >>
  `elbl = "__entry"` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def, initial_compile_state_def] >> strip_tac >> gvs[]) >>
  `MEM (set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K context$global_nonreentrant_slot)
        (mut,nr,rr,name,args,([] : vyperAST$expr list),ret,fbody))) extpkgs` by
    (qpat_assum `extpkgs = _` SUBST1_TAC >>
     simp[MEM_MAP] >> qexists_tac `(mut,nr,rr,name,args,([] : vyperAST$expr list),ret,fbody)` >>
     simp[combinTheory.o_DEF]) >>
  Cases_on `set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K context$global_nonreentrant_slot)
        (mut,nr,rr,name,args,([] : vyperAST$expr list),ret,fbody))` >>
  PairCases_on `r` >>
  rename1 `set_external_package_target _ _ = (lbl,ce,pos,mincd,pay,nr',key,ut,iv,pbody,rt)` >>
  `lbl = "fn_" ++ name /\ nr' = nr /\ pbody = fbody` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[NoAsms, package_external_fn_def, set_external_package_target_def, LET_THM] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `lbl = _` SUBST_ALL_TAC >>
  qpat_x_assum `nr' = nr` SUBST_ALL_TAC >>
  qpat_x_assum `pbody = fbody` SUBST_ALL_TAC >>
  qpat_x_assum `elbl = _` SUBST_ALL_TAC >>
  qpat_x_assum `tys = _` SUBST_ALL_TAC >>
  drule_all none_selected_package_metadata >> strip_tac >>
  suspend "placement"
QED

Resume none_selected_check_prefix[lookup]:
  drule_all classified_external_source_lookup >> strip_tac >>
  Cases_on `rawdefaults` >> gvs[subst_consts_expr_def] >> metis_tac[]
QED

Resume none_selected_check_prefix[placement]:
  qpat_x_assum `MEM ("fn_" ++ name,_,_,_,_,_,_,_,_,_,_) extpkgs` mp_tac >>
  rewrite_tac[MEM_SPLIT] >>
  disch_then (qx_choosel_then [`pre`,`post`] SUBST_ALL_TAC) >>
  drule_all external_selected_check_interval >> strip_tac >>
  `external_fn_shape_ok ("fn_" ++ name,ce,pos,mincd,pay,nr,key,ut,iv,fbody,rt)` by
    fs[EVERY_APPEND] >>
  fs[external_fn_shape_ok_def] >>
  drule_all external_function_registration_boundary >>
  disch_then (qx_choosel_then [`registered_env`,`registered`] strip_assume_tac) >>
  drule register_positional_args_suffix_extends >> strip_tac >>
  `cs_extends after external_st` by
    (drule_all compile_external_function_body_shape >>
     simp[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
     irule (cj 2 external_bodies_run_shape) >>
     simp[] >> qexists_tac `post` >> simp[]) >>
  `fn_has_code opened checked func /\ fn_has_code checked registered func` by
    (conj_tac >> irule fn_has_code_mid >>
     simp[] >> qexistsl_tac [`external_st`,`dispatch_st`] >>
     simp[] >> metis_tac[cs_extends_trans]) >>
  qpat_assum `new_block _ before = (_,opened)`
    (strip_assume_tac o MATCH_MP new_block_props) >>
  `dispatch_st.cs_next_var <= opened.cs_next_var` by
    (qspec_then `pre` mp_tac compile_external_fn_bodies_shape >>
     simp[shape_step_def] >> disch_then drule >>
     simp[shape_extends_def]) >>
  suspend "execution"
QED

Resume none_selected_check_prefix[execution]:
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
    vs_inst_idx := 0|>` >>
  `fresh_vars_wrt label_st ss /\ ~ss.vs_halted /\ allocas_from 0 ss /\
     LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`, `"__entry"`, `label_st`] mp_tac) >>
     simp[Abbr `ss`]) >>
  `EVERY (\(sel,lbl). sel < 2 ** 32)
    (MAP (\(sel,lbl,z). (sel,lbl)) sels)` by
    (qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
       mp_tac linear_selectors_lt >> simp[]) >>
  `linear_dispatch_target ss.vs_call_ctx.cc_calldata
    (MAP (\(sel,lbl,z). (sel,lbl)) sels) fallback = "fn_" ++ name` by
    (drule_all default_raw_selected_target >> simp[Abbr `ss`]) >>
  `!bb. lookup_block ("fn_" ++ name) func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule lowering_context_ok_block_phi >> metis_tac[]) >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp ss` by
    (strip_tac >> irule initial_entry_allocas_below_fmp >>
     goal_assum (drule_at Any) >> simp[Abbr `ss`,vars_pc_only_def]) >>
  drule compile_selector_dispatch_linear_ptr_endpoint >>
  disch_then (qspecl_then [`entry_taint`, `ss`, `0`, `func`] mp_tac) >>
  disch_then (qspecl_then [`unit.cu_context`, `[]`, `FEMPTY`] mp_tac) >>
  (impl_tac >- simp[Abbr `ss`]) >>
  disch_then (qx_choosel_then [`t`,`dispatch_prov`,`dispatch_taint`] strip_assume_tac) >>
  `fresh_vars_wrt opened t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `dispatch_st` >> simp[]) >>
  `vars_pc_only vs t` by
    (irule vars_pc_only_trans >> qexists_tac `ss` >> simp[Abbr `ss`,vars_pc_only_def]) >>
  drule vars_pc_only_fields >> strip_tac >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp t` by
    (qpat_assum `vars_pc_only ss t`
      (mp_tac o AP_TERM ``allocas_below_fmp`` o REWRITE_RULE [vars_pc_only_def]) >>
     qpat_assum `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp ss` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> tautLib.TAUT_TAC) >>
  `allocas_from 0 t` by (drule vars_pc_only_allocas >> fs[allocas_from_def]) >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  `phi_prefix_length b0.bb_instructions = 0 /\
   entry_prov func ss FEMPTY = FEMPTY /\
   entry_taint_vars func ss entry_taint = entry_taint` by
    (Cases_on `b0.bb_instructions` >>
     gvs[get_instruction_def, mk_inst_def, phi_prefix_length_def,
       entry_prov_def, entry_taint_vars_def, phis_prov_def, phis_taint_def,
       Abbr `ss`]) >>
  qexistsl_tac [`rr`,`ce`,`pay`,`key`,`ut`,`iv`,`rt`,`opened`,`checked`,
    `registered_env`,`registered`,`t`,`dispatch_prov`,`dispatch_taint`] >>
  gvs[block_is_terminated_def, Abbr `ss`, entry_taint_def] >>
  asm "compiled_body" (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  conj_tac
  >- (qpat_assum `MEM (mut,nr,rr,name,args,[],ret,fbody) _`
        (mp_tac o ONCE_REWRITE_RULE [MEM_SPLIT]) >>
      simp[NoAsms]) >>
  first_assum ACCEPT_TAC
QED
Finalise none_selected_check_prefix
