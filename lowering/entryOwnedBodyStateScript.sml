(* Body-state constructors that preserve the actual owned endpoint. *)
Theory entryOwnedBodyState
Ancestors
  entryOwnedSourceLocals entryRuntimeStateBoundary entryRuntimePackageLayout
  entryOwnedBodyResources entryRuntimeContextCode entryOwnedEndpointObservations
  exprLoweringProps abiAllocationHistory compileEnv compileVyper moduleLowering
  entryStateRel e2eDefs vyperContext vyperState vyperInterpreter
  venomInst venomState supportedProgram entrySourceOwnedEndpoint
  entryParameterAdmissibility entryPrefixAllocationResources vyperTypeContract
  entryDecoderStateFrame moduleLoweringProps fragExec

Theorem owned_runtime_stmt_resources[local]:
  state_rel fn ce cx es out /\ alloca_inv out /\
  alloca_room ctx fn out /\ fmp_room ctx fn out /\
  ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  abi_alloca_history (fn_insts fn) out /\ fn_inst_ids_distinct fn ==>
  stmt_state_rel ctx fn ce cx es out
Proof
  strip_tac >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_base_zero_def] >>
  rpt strip_tac >> drule_all abi_alloca_history_function_size >> simp[]
QED

Theorem targeted_registered_module_map[local]:
  set_external_package_target target
    (package_external_fn tops locks keys (mut,nr,rr,name,args,(dflts : expr list),ret,fbody)) =
    (lbl,ce,pa,mc,pay,nr',key,locks',view,fbody',rt) /\
  compile_register_positional_args ce pa off st = (cer,registered) ==>
  !name. FLOOKUP cer.ce_module_vars (NONE,name) =
    FLOOKUP (add_immutable_locations
      (get_struct_fields (make_struct_fields_map tops)) tops 0
      (add_module_var_locations tops FEMPTY)) (NONE,name)
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  `cer.ce_module_vars = ce.ce_module_vars` by
    (qpat_x_assum `cer = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[] >>
  Cases_on `ret = NoneT` >>
  gvs[set_external_package_target_def, package_external_fn_def,
    update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
    build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem owned_runtime_body_state:
  lower_vyper_runtime_unit tops pol = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  set_external_package_target target
    (package_external_fn tops locks keys (mut,nr,rr,name,args,(dflts : expr list),ret,fbody)) =
    (lbl,ce,pa,mc,pay,nr',key,locks',view,fbody',rt) /\
  compile_register_positional_args ce pa 4 st = (cer,registered) /\
  entry_decoder_obs vs out /\ local_ptrs_rel fn cer [env] out /\
  alloca_inv out /\ alloca_frontier_inv unit.cu_context fn site out /\
  abi_alloca_history (fn_insts fn) out /\ fn_inst_ids_distinct fn ==>
  stmt_state_rel unit.cu_context fn cer
    (initial_evaluation_context am.sources am.layouts tx NONE) es out /\
  local_ptrs_reserved cer registered /\ cer.ce_return_buf = NONE /\
  out.vs_gas_readings = vs.vs_gas_readings
Proof
  strip_tac >> drule targeted_external_package_layout >> strip_tac >>
  drule_all registered_runtime_layout >> strip_tac >>
  drule_all targeted_registered_locals >> strip_tac >>
  drule_all targeted_registered_module_map >> strip_tac >>
  `storage_vars_rel cer (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel cer (initial_evaluation_context am.sources am.layouts tx NONE)` by
    (irule runtime_entry_storage_vars_rel >>
     simp[initial_evaluation_context_def] >>
     qexistsl [`am`, `tops`, `tx`] >>
     metis_tac[source_typing_ok_vtype_keys_distinct, supported_program_def]) >>
  `state_rel fn cer (initial_evaluation_context am.sources am.layouts tx NONE) es out` by
    (irule runtime_entry_state_rel >> simp[] >>
     qpat_assum `send_call_value _ _ _ = _` (irule_at Any) >>
     qexists_tac `tops` >> simp[initial_evaluation_context_def]) >>
  drule_all runtime_owned_endpoint_alloca_room >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule_all entry_runtime_context_fmp_room >> disch_then (qspec_then `out` assume_tac) >>
  simp[entry_decoder_obs_gas_readings] >>
  irule owned_runtime_stmt_resources >> simp[]
QED

Theorem source_selected_owned_body_state:
  lower_vyper_runtime_unit tops rp = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?lbl ce pa mc pay key tr view rt sc sk cer registered completed t out.
    set_external_package_target rp.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,lookup_raw_return_or_F (NONE : num option)
          tx.function_name External tops,tx.function_name,args,([] : expr list),ret,fbody)) =
      (lbl,ce,pa,mc,pay,F,key,tr,view,fbody,rt) /\
    compile_entry_checks mc pay sc = ((),sk) /\ sc.cs_current_insts = [] /\
    sc.cs_current_bb = lbl /\ fn_has_code sc sk efn /\
    compile_register_positional_args ce pa 4 sk = (cer,registered) /\
    compile_guarded_body cer F key tr view fbody rt registered = ((),completed) /\
    fn_has_code registered completed efn /\ fn_has_code sk registered efn /\
    fn_has_code sk completed efn /\ cs_extends sk registered /\
    fn_inst_ids_distinct efn /\ ~block_is_terminated registered /\
    vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) t /\
    fresh_vars_wrt sk t /\ ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
    t.vs_inst_idx = LENGTH sk.cs_current_insts /\ alloca_history efn t /\
    alloca_inv out /\ alloca_frontier_inv unit.cu_context efn site out /\
    alloca_history efn out /\ abi_alloca_history (fn_insts efn) out /\
    fresh_vars_wrt registered out /\
    (!id. registered.cs_next_id <= id ==> FLOOKUP out.vs_allocas id = NONE) /\
    ~out.vs_halted /\ out.vs_current_bb = registered.cs_current_bb /\
    out.vs_inst_idx = LENGTH registered.cs_current_insts /\ entry_decoder_obs t out /\
    stmt_state_rel unit.cu_context efn cer
      (initial_evaluation_context am.sources am.layouts tx NONE) es0 out /\
    local_ptrs_reserved cer registered /\ cer.ce_return_buf = NONE /\
    out.vs_gas_readings = vs.vs_gas_readings /\
    ((!fuel. mem_safe_run fuel unit.cu_context efn out) ==>
      !fuel. mem_safe_run fuel unit.cu_context efn t) /\
    (!fuel r. run_from fuel unit.cu_context efn out = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' unit.cu_context efn t = r /\
        (mem_safe_run fuel unit.cu_context efn out ==>
         mem_safe_run fuel' unit.cu_context efn t)) /\
    ((!fuel. mem_safe_run fuel unit.cu_context efn out) ==>
      !fuel. mem_safe_blocks fuel unit.cu_context efn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>))
Proof
  strip_tac >> drule_all source_selected_owned_endpoint >>
  disch_then (qspec_then `site` strip_assume_tac) >>
  drule_all selected_external_params_ok >> strip_tac >>
  `ALL_DISTINCT (MAP FST args)` by fs[params_ok_def] >>
  drule_all runtime_entry_allocation_code_resources >> strip_tac >>
  `entry_decoder_obs vs out` by
    (irule entry_owned_endpoint_observations >>
     qexistsl [`elbl`, `t`] >> simp[]) >>
  `local_ptrs_rel efn cer [env] out` by
    (irule owned_source_arguments_local_ptrs >> simp[] >>
     reverse conj_tac
     >- (qexistsl [`unit.cu_context`, `site`] >> simp[]) >>
     qpat_assum `set_external_package_target _ _ = _` (irule_at Any) >>
     qpat_assum `compile_register_positional_args _ _ _ _ = _` (irule_at Any) >>
     simp[] >>
     qpat_assum `LIST_REL _ (MAP _ _) outputs` (irule_at Any) >>
     qpat_assum `LIST_REL _ args values` (irule_at Any) >> simp[]) >>
  drule_all owned_runtime_body_state >> strip_tac >>
  qexistsl [`lbl`, `ce`, `pa`, `mc`, `pay`, `key`, `tr`, `view`, `rt`,
    `sc`, `sk`, `cer`, `registered`, `completed`, `t`, `out`] >> simp[]
QED
