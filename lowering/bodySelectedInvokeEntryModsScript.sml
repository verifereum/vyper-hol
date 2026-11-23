Theory bodySelectedInvokeEntryMods
Ancestors
  bodyFullShadowBodyInv bodyFullShadowInternalCode compileUnit intCallLookup
  fragGasFocus venomExecProps emitHelperProps fmpAnalysisProps
  vyperCompiler venomInst list compileEnv moduleLowering constSubstMods
  compileVyper pair

(* The descriptor list here is the list that extraction actually packaged. *)
Theorem packaged_invoke_entry_label[local]:
  extract_context_with_internals root ips final = SOME (raw,data) /\
  ALL_DISTINCT (ctx_fn_names raw) /\ lbl <> root /\
  lookup_function lbl raw.ctx_functions = SOME callee ==>
  fn_entry_label callee = SOME lbl
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ips))` by
    (drule_then assume_tac extract_context_internal_names >> fs[ctx_fn_names_def]) >>
  qpat_x_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
  simp[extract_context_with_internals_def, AllCaseEqs()] >> strip_tac >>
  gvs[mk_venom_context_def, ctx_fn_names_def, lookup_function_def,
      FIND_thm, mk_raw_function_def] >>
  fs[GSYM lookup_function_def] >>
  drule_then assume_tac lookup_function_MEM >>
  drule_then assume_tac lookup_function_name >>
  drule_then assume_tac package_internal_blocks_metadata >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  rename1 `internal_fn_matches_descriptor desc callee` >> PairCases_on `desc` >>
  gvs[internal_fn_matches_descriptor_def] >>
  drule_all package_internal_blocks_mem >> strip_tac >>
  drule_all lookup_function_distinct_mem >>
  gvs[mk_internal_function_metadata] >>
  disch_then (mp_tac o Q.AP_TERM `\f. f.fn_blocks`) >>
  simp[mk_internal_function_metadata] >> strip_tac >>
  simp[fn_entry_label_def, entry_block_def, NULL_EQ]
QED

Theorem runtime_packaged_invoke_entry[local]:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\ lbl <> "__entry" /\
  lookup_function lbl unit.cu_context.ctx_functions = SOME callee ==>
  fn_entry_label callee = SOME lbl
Proof
  Cases_on `classify_functions_unit mods exps` >>
  rename1 `classify_functions_unit _ _ = classified` >> PairCases_on `classified` >>
  simp[lower_vyper_runtime_unit_mods_def, AllCaseEqs()] >>
  strip_tac >> gvs[run_lowering_def, run_grouped_lowering_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  drule packaged_invoke_entry_label >> fs[lowering_context_ok_def]
QED

Theorem deploy_packaged_invoke_entry[local]:
  lower_vyper_deploy_unit_mods mods exps rp bc = SOME unit /\ lbl <> "__deploy" /\
  lookup_function lbl unit.cu_context.ctx_functions = SOME callee ==>
  fn_entry_label callee = SOME lbl
Proof
  Cases_on `classify_functions_unit mods exps` >>
  rename1 `classify_functions_unit _ _ = classified` >> PairCases_on `classified` >>
  simp[lower_vyper_deploy_unit_mods_def, AllCaseEqs()] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[run_deploy_lowering_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  drule packaged_invoke_entry_label >>
  fs[lowering_context_ok_def, ctx_fn_names_def, install_immutable_reservation_def]
QED

Theorem decoded_invoke_entry[local]:
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,ops) /\ eval_operands ops t = SOME argv ==>
  ~t.vs_halted /\ inst.inst_opcode = INVOKE /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  ?setup first phi_state.
    setup_callee callee argv t = SOME setup /\
    lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
    eval_phis setup first.bb_instructions = OK phi_state /\
    ~phi_state.vs_halted /\
    entered = phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions
Proof
  simp[gas_invoke_entry_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`setup`, `first`, `phi_state`] >> simp[]
QED

Theorem invoke_setup_at_entry[local]:
  setup_callee callee argv t = SOME setup /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  fn_entry_label callee = SOME lbl ==>
  setup.vs_current_bb = lbl /\ setup.vs_inst_idx = 0 /\
  entry_block callee = SOME first /\ first.bb_label = lbl
Proof
  strip_tac >> drule_then strip_assume_tac setup_callee_props >>
  Cases_on `callee.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]
QED

(* The lookup consumes the paired-code rule before either compilation cursor
   is used.  The dynamic cursor still carries the actual PHI result. *)
Theorem selected_invoke_entry_cursor_mods:
  ALOOKUP mods src = SOME tops /\
  (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  lbl = internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,name)))
          (nsid_to_string (src,name)) (MAP SND args) cx.in_deploy /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,ops) /\ eval_operands ops t = SOME argv /\
  gas_invoke_entry (ctx,func) t callee entered /\
  (lookup_function lbl ctx.ctx_functions = SOME callee ==>
    ?rpolicy unit label ce params has_rb nr' key trans view ctor ilen
       compiled_ss rt before old entry final sf beforeS oldS entryS finalS.
      (if cx.in_deploy then
         ?rbc. lower_vyper_deploy_unit_mods mods exps rpolicy rbc = SOME unit
       else lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit) /\
      ctx = unit.cu_context /\
      set_internal_package_target rpolicy.rpol_target
        (package_internal_fn_unit mods T (K global_nonreentrant_slot) cx.in_deploy
          (if cx.in_deploy then imm_len_mods mods else 0)
          (src,subst_consts_fn_mods (consts_env_mods mods)
            (mut,nr,rr,name,args,dflts,ret,ss))) =
        (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt) /\
      compiled_ss = subst_consts_stmts_mods (consts_env_mods mods) ss /\
      new_block label before = (old,entry) /\
      compile_internal_function ce params has_rb nr' key trans view ctor ilen
        compiled_ss rt entry = ((),final) /\
      fn_has_code entry final callee /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
      ctx_inst_ids_distinct ctx /\
      MEM sf shadow_ctx.ctx_functions /\ gas_shadow_function callee sf /\
      new_block label beforeS = (oldS,entryS) /\
      compile_internal_function (gas_shadow_env T ce) params has_rb nr' key
        trans view ctor ilen (MAP gas_shadow_stmt compiled_ss) rt entryS =
        ((),finalS) /\
      gas_shadow_state entry entryS /\ gas_shadow_state final finalS /\
      fn_has_code entryS finalS sf) ==>
  ~t.vs_halted /\ inst.inst_opcode = INVOKE /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  fn_entry_label callee = SOME lbl /\
  ?setup first phi_state rpolicy unit ce params has_rb nr' key trans view ctor ilen
     compiled_ss rt before old entry final sf beforeS oldS entryS finalS.
    setup_callee callee argv t = SOME setup /\
    setup.vs_current_bb = lbl /\ setup.vs_inst_idx = 0 /\
    entry_block callee = SOME first /\ first.bb_label = lbl /\
    lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
    eval_phis setup first.bb_instructions = OK phi_state /\
    ~phi_state.vs_halted /\
    entered = phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions /\
    (if cx.in_deploy then
       ?rbc. lower_vyper_deploy_unit_mods mods exps rpolicy rbc = SOME unit
     else lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit) /\
    ctx = unit.cu_context /\
    set_internal_package_target rpolicy.rpol_target
      (package_internal_fn_unit mods T (K global_nonreentrant_slot) cx.in_deploy
        (if cx.in_deploy then imm_len_mods mods else 0)
        (src,subst_consts_fn_mods (consts_env_mods mods)
          (mut,nr,rr,name,args,dflts,ret,ss))) =
      (lbl,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt) /\
    compiled_ss = subst_consts_stmts_mods (consts_env_mods mods) ss /\
    new_block lbl before = (old,entry) /\
    entry.cs_current_bb = lbl /\ entry.cs_current_insts = [] /\
    compile_internal_function ce params has_rb nr' key trans view ctor ilen
      compiled_ss rt entry = ((),final) /\
    fn_has_code entry final callee /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
    ctx_inst_ids_distinct ctx /\
    MEM sf shadow_ctx.ctx_functions /\ gas_shadow_function callee sf /\
    new_block lbl beforeS = (oldS,entryS) /\
    entryS.cs_current_bb = lbl /\ entryS.cs_current_insts = [] /\
    compile_internal_function (gas_shadow_env T ce) params has_rb nr' key
      trans view ctor ilen (MAP gas_shadow_stmt compiled_ss) rt entryS =
      ((),finalS) /\
    gas_shadow_state entry entryS /\ gas_shadow_state final finalS /\
    fn_has_code entryS finalS sf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac decoded_invoke_entry >>
  qpat_x_assum `lookup_function _ _ = _ ==> _` (drule_then strip_assume_tac) >>
  `fn_entry_label callee = SOME lbl` by
    (qpat_x_assum `vis = Internal \/ _` kall_tac >>
     `lbl <> "__entry" /\ lbl <> "__deploy"` by simp[internal_fn_label_def] >>
     Cases_on `cx.in_deploy` >> gvs[]
     >- drule_all_then ACCEPT_TAC deploy_packaged_invoke_entry >>
     drule_all_then ACCEPT_TAC runtime_packaged_invoke_entry) >>
  drule_all_then strip_assume_tac invoke_setup_at_entry >>
  `label = lbl` by
    (qpat_assum `set_internal_package_target _ _ = _` (mp_tac o Q.AP_TERM `FST`) >>
     simp_tac std_ss [subst_consts_fn_mods_def, package_internal_fn_unit_def,
       set_internal_package_target_def, LET_THM, FST] >> simp[]) >>
  qpat_x_assum `label = lbl` SUBST_ALL_TAC >>
  imp_res_tac new_block_props >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`setup`, `first`, `phi_state`, `rpolicy`, `unit`, `ce`, `params`,
    `has_rb`, `nr'`, `key`, `trans`, `view`, `ctor`, `ilen`, `compiled_ss`, `rt`,
    `before`, `old`, `entry`, `final`, `sf`, `beforeS`, `oldS`, `entryS`, `finalS`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
