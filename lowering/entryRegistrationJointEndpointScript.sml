(* One selected ready state and its owned registration endpoint. *)
Theory entryRegistrationJointEndpoint
Ancestors
  entryCheckEndpointMem entrySourceRegistrationFold entryCompletedExitPhi
  entryDispatchMem actualRegistrationCode fragExec guardedBodyFirstEmission
  exprLoweringProps venomState compileEnv moduleLoweringProps abiAllocationHistory

Theorem selected_entry_registration_endpoint:
  compile_selector_dispatch_linear sels fl sf = ((),sd) /\
  fn_has_code sf sd fn /\ EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  compile_entry_checks mc pay sc = ((),st) /\ fn_has_code sc st fn /\
  sd.cs_next_var <= sc.cs_next_var /\ sc.cs_current_insts = [] /\
  linear_dispatch_target s.vs_call_ctx.cc_calldata sels fl = sc.cs_current_bb /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  mc <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts /\ sf.cs_current_insts = [] /\
  s.vs_allocas = FEMPTY /\
  compile_register_positional_args ce specs 4 st = (cer,registered) /\
  compile_guarded_body cer F nk ut iv stmts rt registered = ((),completed) /\
  ~block_is_terminated registered /\ fn_has_code st completed fn /\
  fn_inst_ids_distinct fn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  registered.cs_next_var <= limit_st.cs_next_var /\
  (!t. vars_pc_only s t /\ fresh_vars_wrt st t /\
    ~t.vs_halted /\ t.vs_current_bb = st.cs_current_bb /\
    t.vs_inst_idx = LENGTH st.cs_current_insts ==>
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    fresh_vars_wrt limit_st t /\
    (!id. st.cs_next_id <= id ==> FLOOKUP t.vs_allocas id = NONE) /\
    mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD t) = bs) /\
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    abi_decoder_coherent ce env fields ty tv /\
    info = type_to_abi_dec_info fields ce ty /\
    sz = abi_embedded_static_size ce.ce_struct_fields ty /\ sz = abi_member_head_size at /\
    type_memory_bytes ce ty = type_memory_size tv /\
    (prim ==> ?c. info = DecPrimWord c) /\ (dyn /\ ~prim <=> is_dynamic at) /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    at = vyper_to_abi_type env ty /\ type_memory_size tv < dimword (:256)) specs values /\
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) specs values /\
  ALL_DISTINCT (MAP (\(name,prim,dyn,sz,info). name) specs) /\
  has_types (MAP (\(ty,tv,v,at,av). at) values) (MAP (\(ty,tv,v,at,av). av) values) /\
  bs = enc (Tuple (MAP (\(ty,tv,v,at,av). at) values))
    (ListV (MAP (\(ty,tv,v,at,av). av) values)) /\
  4 + LENGTH bs < dimword (:256) ==>
  ?t out outputs.
    vars_pc_only s t /\ fresh_vars_wrt st t /\
    ~t.vs_halted /\ t.vs_current_bb = st.cs_current_bb /\
    t.vs_inst_idx = LENGTH st.cs_current_insts /\ alloca_history fn t /\
    alloca_inv out /\ alloca_frontier_inv ctx fn site out /\
    alloca_history fn out /\ abi_alloca_history (fn_insts fn) out /\
    fresh_vars_wrt limit_st out /\
    (!id. registered.cs_next_id <= id ==> FLOOKUP out.vs_allocas id = NONE) /\
    ~out.vs_halted /\ out.vs_current_bb = registered.cs_current_bb /\
    out.vs_inst_idx = LENGTH registered.cs_current_insts /\
    entry_decoder_obs t out /\
    ((!fuel. mem_safe_run fuel ctx fn out) ==> !fuel. mem_safe_run fuel ctx fn t) /\
    (!fuel r. run_from fuel ctx fn out = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn t = r /\
        (mem_safe_run fuel ctx fn out ==> mem_safe_run fuel' ctx fn t)) /\
    LIST_REL (\(name,tv,v) (dst,p,id).
      FLOOKUP cer.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
      (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
        ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\ ins.inst_id = id) /\
      id < registered.cs_next_id /\ abi_decoder_operand_live registered.cs_next_var dst /\
      FLOOKUP out.vs_allocas id = SOME (p,type_memory_size tv) /\
      eval_operand dst out = SOME (n2w p) /\
      val_wf tv v /\ val_in_memory tv v p out.vs_memory)
      (MAP (\((name,prim,dyn,sz,info),(ty,tv,v,at,av)). (name,tv,v))
        (ZIP (specs,values))) outputs /\
    ALL_DISTINCT (MAP (\(dst,p,id). id) outputs) /\
    ((!fuel. mem_safe_run fuel ctx fn out) ==> !fuel. mem_safe_blocks fuel ctx fn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all selected_dispatch_checks_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `alloca_history fn t` by metis_tac[] >>
  qpat_x_assum `!t. vars_pc_only s t /\ _ ==> _`
    (qspec_then `t` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  drule_all entry_registration_source_endpoint >> strip_tac >>
  `t.vs_allocas = FEMPTY` by fs[vars_pc_only_def, venom_state_component_equality] >>
  `abi_alloca_history (fn_insts fn) t` by simp[abi_alloca_history_empty] >>
  `abi_alloca_history (fn_insts fn) out` by metis_tac[] >>
  qexistsl_tac [`t`,`out`,`outputs`] >> simp[] >>
  suspend "safety"
QED

Resume selected_entry_registration_endpoint[safety]:
  strip_tac >>
  `!n. mem_safe_run n ctx fn t` by metis_tac[] >>
  qpat_x_assum `(_ /\ _) ==> !n. mem_safe_blocks n ctx fn s` irule >>
  simp[] >> strip_tac >>
  `st.cs_current_insts = []` by fs[] >>
  `cs_extends st completed` by
    (drule register_positional_args_suffix_extends >>
     drule_all guarded_body_first_emission >>
     metis_tac[cs_extends_trans]) >>
  drule_all fn_has_code_start >> strip_tac >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (drule_all registration_guarded_suffix_empty_phi >> metis_tac[]) >>
  irule mem_safe_blocks_no_phi >>
  simp[eval_phis_no_phi] >>
  `t with vs_inst_idx := 0 = t` by simp[venom_state_component_equality] >>
  simp[]
QED

Finalise selected_entry_registration_endpoint
