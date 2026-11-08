(* Source-selected registration: one actual owned endpoint and its safety continuation. *)
Theory entrySourceOwnedEndpoint
Ancestors
  entrySelectedCompilerInputs entrySelectedOwnershipInputs entrySelectedCalldataWindow
  entryRegistrationJointEndpoint entryReadyRegistrationResources
  entryPrefixAllocationResources entryDispatchProps moduleLoweringProps compileEnv fragExec list

Theorem source_selected_owned_endpoint:
  lower_vyper_runtime_unit tops rp = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE) es = (INL (),es') /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?lbl ce pa mc pay key tr view rt sc sk cer registered completed values t out outputs.
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
    fn_inst_ids_distinct efn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts efn)) /\
    ~block_is_terminated registered /\
    LIST_REL (\(name,ty) (ty',tv,v,at,av).
      ty' = ty /\ evaluate_type (type_env tops) ty = SOME tv) args values /\
    MAP (\(ty,tv,v,at,av). v) values = tx.args /\
    LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
      abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
      info = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
      sz = abi_embedded_static_size ce.ce_struct_fields ty /\ sz = abi_member_head_size at /\
      type_memory_bytes ce ty = type_memory_size tv /\
      (prim ==> ?c. info = DecPrimWord c) /\ (dyn /\ ~prim <=> is_dynamic at) /\
      value_has_type tv v /\ vyper_to_abi (type_env tops) ty v = SOME av /\
      at = vyper_to_abi_type (type_env tops) ty /\
      type_memory_size tv < dimword (:256)) pa values /\
    vs.vs_call_ctx.cc_calldata =
      function_selector tx.function_name (MAP (\(ty,tv,v,at,av). at) values) ++
      enc (Tuple (MAP (\(ty,tv,v,at,av). at) values))
        (ListV (MAP (\(ty,tv,v,at,av). av) values)) /\
    vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) t /\
    fresh_vars_wrt sk t /\ ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
    t.vs_inst_idx = LENGTH sk.cs_current_insts /\ alloca_history efn t /\
    alloca_inv out /\ alloca_frontier_inv unit.cu_context efn site out /\
    alloca_history efn out /\ fresh_vars_wrt registered out /\
    (!id. registered.cs_next_id <= id ==> FLOOKUP out.vs_allocas id = NONE) /\
    ~out.vs_halted /\ out.vs_current_bb = registered.cs_current_bb /\
    out.vs_inst_idx = LENGTH registered.cs_current_insts /\ entry_decoder_obs t out /\
    ((!fuel. mem_safe_run fuel unit.cu_context efn out) ==>
      !fuel. mem_safe_run fuel unit.cu_context efn t) /\
    (!fuel r. run_from fuel unit.cu_context efn out = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' unit.cu_context efn t = r /\
        (mem_safe_run fuel unit.cu_context efn out ==>
         mem_safe_run fuel' unit.cu_context efn t)) /\
    LIST_REL (\(name,tv,v) (dst,p,id).
      FLOOKUP cer.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
      id < registered.cs_next_id /\ abi_decoder_operand_live registered.cs_next_var dst /\
      FLOOKUP out.vs_allocas id = SOME (p,type_memory_size tv) /\
      eval_operand dst out = SOME (n2w p) /\
      val_wf tv v /\ val_in_memory tv v p out.vs_memory)
      (MAP (\((name,prim,dyn,sz,info),(ty,tv,v,at,av)). (name,tv,v))
        (ZIP (pa,values))) outputs /\
    ALL_DISTINCT (MAP (\(dst,p,id). id) outputs) /\
    ((!fuel. mem_safe_run fuel unit.cu_context efn out) ==>
      !fuel. mem_safe_blocks fuel unit.cu_context efn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>))
Proof
  strip_tac >> drule_all source_selected_compiler_inputs >> strip_tac >>
  drule_all selected_external_owned_descriptor_values >> strip_tac >>
  drule_all runtime_entry_allocation_code_resources >> strip_tac >>
  suspend "endpoint"
QED

Resume source_selected_owned_endpoint[endpoint]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>)
    (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>)` by
    simp[vars_pc_only_def, venomStateTheory.venom_state_component_equality] >>
  drule_all selected_ready_calldata_window >> strip_tac >>
  `!t. vars_pc_only
       (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) t /\
       fresh_vars_wrt sk t /\ ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
       t.vs_inst_idx = LENGTH sk.cs_current_insts ==>
       alloca_inv t /\ alloca_frontier_inv unit.cu_context efn site t /\
       fresh_vars_wrt registered t /\
       (!id. sk.cs_next_id <= id ==> FLOOKUP t.vs_allocas id = NONE) /\
       mem_bytes_at 4
         (LENGTH (enc (Tuple (MAP (\(ty,tv,v,at,av). at) values))
           (ListV (MAP (\(ty,tv,v,at,av). av) values))))
         (abi_decode_source CALLDATALOAD t) =
       enc (Tuple (MAP (\(ty,tv,v,at,av). at) values))
         (ListV (MAP (\(ty,tv,v,at,av). av) values))` by
    (rpt strip_tac >> drule_all runtime_ready_registration_resources >>
     disch_then (qspec_then `site` strip_assume_tac) >>
     drule_all selected_ready_calldata_window >> simp[]) >>
  suspend "apply_endpoint"
QED
Resume source_selected_owned_endpoint[apply_endpoint]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qexistsl [`lbl`, `ce`, `pa`, `mc`, `pay`, `key`, `tr`, `view`, `rt`,
            `sc`, `sk`, `cer`, `registered`, `completed`, `values`] >>
  simp[] >>
  irule (SRULE [] selected_entry_registration_endpoint) >>
  gvs[] >> simp[SF SFY_ss] >>
  goal_assum (drule_at (Pat `compile_selector_dispatch_linear _ _ _ = _`)) >>
  simp[] >>
  goal_assum (drule_at (Pat `compile_entry_checks _ _ _ = _`)) >> simp[]
QED
Finalise source_selected_owned_endpoint
