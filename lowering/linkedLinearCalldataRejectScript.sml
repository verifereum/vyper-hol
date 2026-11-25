(* The linked linear selector hit reduces to the common ABI rejection path. *)
Theory linkedLinearCalldataReject
Ancestors
  linkedExternalParameterTypes linkedLinearSelectedCode linkedLinearDispatchPath
  linkedEntryCheckResources linkedRegistrationPackageInputs linkedRawUnitShape
  dispatchedSignatureMemberMods dispatchedClassifiedRouteMods defaultDispatchModsRun
  acceptedContextPhi calldataNoneSelectedChecks callRejectMemory entryJointRevertExit
  defaultConcreteRegistrationDefs entryPrefixPtr exprLoweringProps allocaFrontierBound
  actualEntryAllocationFrame allocaFrontierRoom
  e2eModsDefs sourceUnitExecutionMods vyperLoweringCorrect
  compileUnit compileVyper compileEnv vyperCompiler moduleLoweringProps
  entryDispatchProps emitHelperProps fragGasOriginPtrLoop fragGasOriginPtr fragGasPathPtr
  fragGasPathMem ptrDiscipline venomExecSemantics venomInst venomState
  venomInstIdsProps vyperTypeContractContext vyperTypeContract vyperCalldata constSubstMods
  finite_map list pair arithmetic words
Theorem lower_vyper_runtime_unit_linear_hit_reverts_mods:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  source_typing_ok_mods mods exps am tx /\
  initial_venom_state_rel_mods mods am tx vs /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
  ~EXISTS (external_has_defaults o SND) exts /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys =
    cd_selector vs.vs_call_ctx.cc_calldata) (abi_deployed_signatures mods exps) =
      SOME (name,tys) /\
  calldata_dispatch_mods mods exps vs.vs_call_ctx.cc_calldata = NONE /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) ==>
  ?fn s G tn.
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__entry" /\
    s.vs_returndata = [] /\
    (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
    gas_path_mem unit.cu_context fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>) 0 (Abort Revert_abort s) /\
    (!D. gas_path_ptr D 0 unit.cu_context fn [] FEMPTY entry_taint
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
      0 G tn (Abort Revert_abort s)) /\
    (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (name,tys) (abi_deployed_signatures mods exps)` by
    (drule FIND_MEM >> simp[]) >>
  drule_all deployed_default_free_signature_member >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  rename1 `MEM (_,(_,_,_,name,args,[],ret,
    subst_consts_stmts_mods (consts_env_mods mods) decl_body)) exts` >>
  `params_ok (type_env_all_modules mods) args` by
    (irule checked_external_parameter_types_mods >>
     rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  `contract_namespaces_ok F mods /\ call_tx_well_typed tx` by
    (qpat_assum `source_typing_ok_mods _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [source_typing_ok_mods_def]) >>
     drule_then assume_tac check_contract_namespaces_ok >> simp[]) >>
  qabbrev_tac `src = ALOOKUP exps name` >>
  qabbrev_tac `code = subst_consts_stmts_mods (consts_env_mods mods) decl_body` >>
  `MEM (src,(mut,nr,rr,name,args,([]:expr list),ret,code)) exts` by
    simp[Abbr `src`, Abbr `code`] >>
  `fn_allocs_ok_unit mods (src,(mut,nr,rr,name,args,([]:expr list),ret,code))` by
    (qpat_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
     qpat_assum `classify_functions_unit _ _ = _` (fn classified =>
       simp_tac (srw_ss()) [lower_vyper_runtime_unit_mods_def, LET_THM,
         classified, AllCaseEqs(), EVERY_APPEND, EVERY_MEM]) >>
     metis_tac[]) >>
  `?lbl ce pos mc pay key tr view rt.
    set_external_package_target rp.rpol_target
      (package_external_fn_unit mods T (K global_nonreentrant_slot)
        (src,(mut,nr,rr,name,args,([]:expr list),ret,code))) =
      (lbl,ce,pos,mc,pay,nr,key,tr,view,code,rt)` by
    (Cases_on `ret = NoneT` >>
     simp[set_external_package_target_def, package_external_fn_unit_def]) >>
  drule_all linked_registration_package_inputs >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `tvs` strip_assume_tac)))) >>
  drule_all linked_linear_selected_registration_code >>
  disch_then (qx_choosel_then [`fn`,`fl`,`ds`,`de`,`opened`,`checked`,
    `registered_env`,`registered`,`last`] strip_assume_tac) >>
  drule_then strip_assume_tac lower_vyper_runtime_unit_raw_shape_mods >>
  qabbrev_tac `sels = MAP (\(sel,l,z). (sel,l))
    (build_selectors (type_env_all_modules mods) (MAP SND exts))` >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                                vs_inst_idx := 0|>` >>
  `EVERY (\(sel,l). sel < 2 ** 32) sels` by
    simp[Abbr `sels`, linear_selectors_lt] >>
  `linear_dispatch_target vs.vs_call_ctx.cc_calldata sels fl = lbl` by
    (drule_all (SRULE [LET_THM] linked_classified_linear_routes) >>
     disch_then (qspec_then `vs.vs_call_ctx.cc_calldata` (mp_tac o cj 2)) >>
     disch_then (qspecl_then [`src`,`mut`,`nr`,`rr`,`name`,`args`,`[]`,`ret`,`code`] mp_tac) >>
     fs[Abbr `sels`]) >>
  `compile_selector_dispatch_linear sels fl ds = ((),de)` by simp[Abbr `sels`] >>
  drule_all linked_linear_dispatch_entry_path >>
  disch_then (qx_choosel_then [`p`,`G0`,`tn0`] strip_assume_tac) >>
  `fresh_vars_wrt opened p` by
    (irule fresh_vars_wrt_mono >> qexists_tac `de` >> simp[]) >>
  `4 <= LENGTH p.vs_call_ctx.cc_calldata` by simp[] >>
  mp_tac (Q.INST [`PG` |-> `[]`, `lo` |-> `0`, `ctx` |-> `unit.cu_context`,
    `s` |-> `p`, `m` |-> `mc`, `tn` |-> `tn0`, `G` |-> `G0`]
    (SPEC_ALL selected_checks_reject_or_continue)) >>
  impl_tac >- simp[] >>
  disch_then assume_tac >>
  suspend "after_checks"
QED

Resume lower_vyper_runtime_unit_linear_hit_reverts_mods[after_checks]:
  `?s G tn. s.vs_returndata = [] /\
      !D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
        (start,FEMPTY,entry_taint) [] (Abort Revert_abort s,G,tn)` suffices_by
    (disch_then (qx_choosel_then [`s`,`G`,`tn`] strip_assume_tac) >>
     qexistsl_tac [`fn`,`s`,`G`,`tn`] >> simp[] >>
     qspecl_then [`unit.cu_context`,`fn`,`vs`,`s`,`G`,`tn`,`[]`]
       mp_tac entry_joint_revert_exit >> fs[Abbr `start`]) >>
  qpat_x_assum `(?z H u. z.vs_returndata = [] /\ _) \/ _`
    (DISJ_CASES_THEN2 (qx_choosel_then [`z`,`G1`,`tn1`] strip_assume_tac)
      (qx_choosel_then [`s`,`G1`,`tn1`] strip_assume_tac))
  >- (qexistsl_tac [`z`,`G1`,`tn1`] >> simp[] >> rpt gen_tac >>
      irule gas_origin_ptr_path_trans >> qexistsl_tac [`G0`,`p`,`tn0`] >>
      fs[Abbr `start`]) >>
  `4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata` by
    metis_tac[] >>
  `~(LENGTH vs.vs_call_ctx.cc_calldata < SUM (MAP tv_abi_size tvs) + 4)` by
    decide_tac >>
  `calldata_decode_args s.vs_call_ctx.cc_calldata tvs 0 = NONE` by
    (qpat_assum `calldata_dispatch_mods _ _ _ = NONE` mp_tac >>
     Cases_on `calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0` >>
     fs[calldata_dispatch_mods_def, arithmeticTheory.NOT_LESS]) >>
  `vars_pc_only vs s` by (irule vars_pc_only_trans >> qexists_tac `p` >> simp[]) >>
  qabbrev_tac `site = ARB:instruction` >>
  `default_registration_resources unit.cu_context fn site 0 checked s tn1` by
    (mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `initial` |-> `vs`,
        `tn` |-> `tn1`, `site` |-> `site`]
        (SPEC_ALL linked_post_checks_resources)) >> simp[]) >>
  `MEM fn unit.cu_context.ctx_functions` by
    (drule_then ACCEPT_TAC venomInstTheory.lookup_function_MEM) >>
  `!bb label. lookup_block label fn.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC lowering_context_ok_block_phi) >>
  `LENGTH args = LENGTH tvs` by
    (drule_then (mp_tac o GSYM) vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  `LIST_REL (\(nm,ty) tv.
     abi_decoder_coherent ce (type_env_all_modules mods) ce.ce_struct_fields ty tv /\
     (?loc. FLOOKUP ce.ce_vars nm = SOME loc /\
       var_location_memory_size loc = SOME (type_memory_size tv)) /\
     type_memory_size tv < dimword (:256)) args tvs` by
    (fs[LIST_REL_EL_EQN] >> simp[] >> gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH tvs ==> _`
       (qspec_then `n` mp_tac) >>
     Cases_on `EL n args` >> simp[EL_ZIP, EL_MAP]) >>
  `s.vs_allocas = FEMPTY` by
    (qpat_assum `vars_pc_only vs s` (mp_tac o MATCH_MP vars_pc_only_allocas) >>
     fs[initial_venom_state_rel_mods_def]) >>
  qpat_assum `default_registration_resources _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [default_registration_resources_def,
       alloca_frontier_inv_from_def, GSYM alloca_frontier_inv_def]) >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp s /\
     s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp` by
    (simp[allocas_below_fmp_def] >> strip_tac >>
     qpat_assum `fmp_room _ _ _` (mp_tac o REWRITE_RULE [fmp_room_def]) >>
     simp[] >> decide_tac) >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by
    (qpat_assum `s.vs_call_ctx = p.vs_call_ctx` (PURE_REWRITE_TAC o single) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `compile_register_positional_args ce (build_positional_args ce args) 4 checked =
    (registered_env,registered)` by
    (qpat_assum `pos = build_positional_args _ _` (fn positional =>
       qpat_assum `compile_register_positional_args ce pos 4 checked = _`
         (ACCEPT_TAC o REWRITE_RULE [positional]))) >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `env` |-> `type_env_all_modules mods`,
      `fn` |-> `fn`, `ce` |-> `ce`, `cef` |-> `registered_env`,
      `args` |-> `args`, `tvs` |-> `tvs`, `sa` |-> `checked`,
      `sb` |-> `registered`, `s` |-> `s`, `site` |-> `site`,
      `G` |-> `G1`, `tn` |-> `tn1`]
    (SPEC_ALL coherent_registration_reject_path)) >>
  impl_tac
  >- (rpt conj_tac >>
      (FIRST_ASSUM ACCEPT_TAC ORELSE simp[alloca_frontier_inv_def])) >>
  disch_then (qx_choosel_then [`z`,`G2`,`tn2`] strip_assume_tac) >>
  qexistsl_tac [`z`,`G2`,`tn2`] >> simp[] >> rpt gen_tac >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G0`,`p`,`tn0`] >>
  fs[Abbr `start`] >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G1`,`s`,`tn1`] >> simp[]
QED

Finalise lower_vyper_runtime_unit_linear_hit_reverts_mods
