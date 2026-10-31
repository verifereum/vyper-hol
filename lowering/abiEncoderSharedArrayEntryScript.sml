Theory abiEncoderSharedArrayEntry
Ancestors
  abiEncoderExtendControl abiEncoderArrayHeader abiEncoderArrayHeaderMemory abiEncoderExtendSim
  abiEncoderVarTransport abiEncoderRegisteredEffect abiDecoderVarExtend execEquivParamDefs
  abiEncoderSharedArrayIndex abiEncoderSharedContract abiDecoderFootprint abiScratchAddress
  abiEncoderMembersDefs abiDecoderLoopRegisters abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderAllocation abiDecoderArrayBackedge abiDecoderLoop abiDecoderContract venomState
  venomExecSemantics venomMemDefs words list arithmetic abiEncoderArrayExit
  abiEncoderArrayContext abiEncoderArrayCode abiEncoderMemberPhaseRaw
  abiEncoderMemberPhaseEffect abiBuiltinPrefix abiScratchEffect abiScratchLeafEffect
  abiDecoderFrame abiEncoderArrayPrefix exprLoweringProps compileEnv emitHelper emitHelperProps
  venomInst venomInstProps instIdxIndep rich_list abiEncoderSharedArrayInitFrame
  abiScratchEncoderContract valueEncodingProps abiDecodeRanges valueEncoding contractABI
  abiEncoderArrayLoopDynamicStep abiEncoderArrayLoopCode abiDecoderPrimitiveLoopEntry

(* Concrete header observations and extension stability on both selected edges. *)
Theorem abi_encoder_array_header_extend_state:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras
    (jump_to label (abi_encode_array_header_state iv cmp done i n s))
    (jump_to label (abi_encode_array_header_state iv cmp done i n t))
Proof
  strip_tac >>
  `abi_decoder_vars_extend extras (abi_encode_array_header_state iv cmp done i n s)
    (abi_encode_array_header_state iv cmp done i n t)` by
    (simp_tac bool_ss [abi_encode_array_header_state_def] >>
     rpt (irule abi_decoder_vars_extend_update) >> asm_rewrite_tac []) >>
  pop_assum mp_tac >>
  simp[abi_decoder_vars_extend_def, jump_to_def, vsr_frame_def,
    venom_state_component_equality, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_encoder_array_header_registered:
  abi_encoder_registered_effect ids outs s
    (jump_to label (abi_encode_array_header_state iv cmp done i n s)) /\
  (alloca_inv s ==> alloca_inv (jump_to label (abi_encode_array_header_state iv cmp done i n s)))
Proof
  simp[abi_encoder_registered_effect_def, jump_to_def, abi_encode_array_header_state_def,
    update_var_def, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_shared_input_address:
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) s /\
  abi_decoder_address_frame st.cs_next_var s t ==>
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) t
Proof
  simp_tac bool_ss [abi_encoder_shared_input_def, abi_decoder_address_frame_def] >>
  strip_tac >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  fs[abi_decoder_child_scratch_def]
QED

Theorem abi_encoder_shared_array_index_address:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin s /\
  abi_decoder_address_frame owner_st.cs_next_var s t /\
  fresh_vars_wrt limit_st t /\ hi <= last /\
  abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] s t /\
  (alloca_inv s ==> alloca_inv t) /\ abi_encoder_extend_sim ctx func s t /\
  t.vs_current_bb = next_label /\ t.vs_inst_idx = 0 ==>
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) next_label j origin t
Proof
  strip_tac >> drule abi_encoder_shared_array_index_facts >> strip_tac >>
  qpat_x_assum `active = is_dynamic ty` kall_tac >>
  qpat_x_assum `asz = abi_member_head_size ty` kall_tac >>
  qpat_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) t` by
    (drule_all abi_encoder_shared_input_address >> simp[]) >>
  `abi_encoder_cursor T ip site slot first site owner_st j t /\
   abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
     (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) t` by
    (conj_tac >> irule abi_encoder_cursor_address >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`s`,`owner_st`] >> full_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap s t` by
    (drule_all abi_scratch_address_effect >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ ~t.vs_halted` by fs[abi_decoder_address_frame_def] >>
  irule abi_encoder_shared_array_index_advance >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`s`,`j`,`label`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_array_header_index:
  lookup_block label func.fn_blocks = SOME <|bb_label := label; bb_instructions :=
    abi_encode_array_header_insts id ip count_op (STRING #"%" (toString owner_st.cs_next_var))
      (STRING #"%" (toString (owner_st.cs_next_var+1)))
      (STRING #"%" (toString (owner_st.cs_next_var+2))) body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  owner_st.cs_next_id <= last /\ owner_st.cs_next_var+3 <= limit_st.cs_next_var /\ hi <= last /\
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin s ==>
  ?t. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz)
    (if j < LENGTH avs then body_lbl else exit_lbl) j origin t /\
    abi_encoder_extend_sim ctx func s t
Proof
  strip_tac >> drule abi_encoder_shared_array_index_facts >> strip_tac >>
  qpat_x_assum `active = is_dynamic ty` kall_tac >>
  qpat_x_assum `asz = abi_member_head_size ty` kall_tac >>
  qpat_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  `count_op <> Var (STRING #"%" (toString owner_st.cs_next_var))` by
    (drule abi_decoder_live_excludes_output >> simp[]) >>
  qabbrev_tac `t = jump_to (if j < LENGTH avs then body_lbl else exit_lbl)
    (abi_encode_array_header_state (STRING #"%" (toString owner_st.cs_next_var))
      (STRING #"%" (toString (owner_st.cs_next_var+1)))
      (STRING #"%" (toString (owner_st.cs_next_var+2))) j (LENGTH avs) s)` >>
  `abi_decoder_address_frame owner_st.cs_next_var s t` by
    simp[Abbr `t`, abi_encode_array_header_address_frame] >>
  `fresh_vars_wrt limit_st t` by
    (simp_tac bool_ss [Abbr `t`, abi_decoder_fresh_jump] >>
     irule abi_encode_array_header_registers >> simp[]) >>
  `abi_encoder_extend_sim ctx func s t` by
    (simp_tac bool_ss [Abbr `t`] >> irule abi_encoder_array_header_extend_sim >>
     asm_simp_tac (srw_ss()) [] >>
     qexistsl_tac [`count_op`,`id`,`ip`,`n2w slot`] >>
     asm_simp_tac bool_ss [] >>
     drule_all abi_encoder_cursor_bounds >> strip_tac >>
     fs[abi_encoder_cursor_def, w2n_n2w]) >>
  `t.vs_current_bb = (if j < LENGTH avs then body_lbl else exit_lbl) /\ t.vs_inst_idx = 0` by
    simp[Abbr `t`, jump_to_def] >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_shared_array_index_address >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`label`,`s`] >> asm_simp_tac bool_ss [] >>
  simp[Abbr `t`, abi_encoder_array_header_registered, jump_to_def,
    abi_encode_array_header_state_def, update_var_def]
QED

(* Read-only generated exits at the common raw endpoint. *)
Theorem abi_encoder_phase_current_bb[local]:
  abi_encoder_member_phase_raw st final initial ready /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final) ==>
  ready.vs_current_bb = initial.vs_current_bb
Proof
  simp_tac bool_ss [abi_encoder_member_phase_raw_def] >> strip_tac >> gvs[] >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
  qexists_tac `emitted_insts st final` >> asm_rewrite_tac [] >> rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem abi_encoder_array_static_exit_raw_transport:
  abi_encode_array_static_exit src asz st = (out,final) /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (n2w (32+cnt*asz)) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = initial.vs_current_bb /\ ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule (CONJUNCT1 abi_encode_array_exit_shape) >> strip_tac >>
  `ready.vs_current_bb = initial.vs_current_bb` by
    (drule_all abi_encoder_phase_current_bb >> simp[]) >>
  drule_all abi_encode_array_static_exit_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def,
    abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> metis_tac[]
QED

Theorem abi_encoder_array_dynamic_exit_raw_transport:
  abi_encode_array_dynamic_exit src dp st = (out,final) /\
  eval_operand src initial = SOME src_word /\ eval_operand dp initial = SOME (n2w slot) /\
  abi_decoder_operand_live st.cs_next_var dp /\ mload slot initial = n2w off /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (n2w (32+off)) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = initial.vs_current_bb /\ ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule (CONJUNCT2 abi_encode_array_exit_shape) >> strip_tac >>
  `ready.vs_current_bb = initial.vs_current_bb` by
    (drule_all abi_encoder_phase_current_bb >> simp[]) >>
  drule_all abi_encode_array_dynamic_exit_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def,
    abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> metis_tac[]
QED

Theorem abi_encoder_array_exit_opcodes:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MUL \/ i.inst_opcode = MLOAD)
    (emitted_insts st final)
Proof
  Cases_on `active` >>
  simp[abi_encode_array_dynamic_exit_def, abi_encode_array_static_exit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_array_exit_extend:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >>
  Cases_on `active` >> gvs[]
  >- (drule (CONJUNCT2 abi_encode_array_exit_shape) >> strip_tac >>
      drule_all abi_encoder_member_phase_extend_sim >> simp[]) >>
  drule (CONJUNCT1 abi_encode_array_exit_shape) >> strip_tac >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED

Theorem abi_encoder_array_exit_readonly:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  ready.vs_memory = initial.vs_memory /\
  ready.vs_allocas = initial.vs_allocas /\ ready.vs_alloca_next = initial.vs_alloca_next /\
  ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
  ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests
Proof
  strip_tac >> drule abi_encoder_array_exit_opcodes >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK u` >>
  ` (u.vs_memory,u.vs_allocas,u.vs_alloca_next,u.vs_accounts,u.vs_transient,u.vs_logs,u.vs_requests) =
    (initial.vs_memory,initial.vs_allocas,initial.vs_alloca_next,initial.vs_accounts,
      initial.vs_transient,initial.vs_logs,initial.vs_requests)` by
    (irule (BETA_RULE (Q.ISPEC
       `\s:venom_state. (s.vs_memory,s.vs_allocas,s.vs_alloca_next,s.vs_accounts,
         s.vs_transient,s.vs_logs,s.vs_requests)` run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts st final` >> asm_rewrite_tac [] >> rpt strip_tac >>
     `i.inst_opcode = ADD \/ i.inst_opcode = MUL \/ i.inst_opcode = MLOAD` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     gvs[step_inst_base_def, exec_pure2_def, exec_read1_def, AllCaseEqs(), update_var_def]) >>
  gvs[]
QED

Theorem abi_encoder_array_exit_registered:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  strip_tac >> drule_all abi_encoder_array_exit_readonly >> strip_tac >>
  simp[abi_encoder_registered_effect_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_array_exit_effect:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  abi_decoder_address_frame st.cs_next_var initial ready /\ fresh_vars_wrt limit_st ready /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial ready /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready) /\ abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule_all abi_encoder_array_exit_readonly >> strip_tac >>
  drule_all abi_encoder_array_exit_registered >>
  disch_then (qspecl_then [`[(d,sz)]`,`abi_decoder_ids lo hi`] strip_assume_tac) >>
  drule_all abi_encoder_array_exit_extend >> disch_then (qspec_then `ctx` assume_tac) >>
  asm_simp_tac bool_ss [] >> irule abi_scratch_leaf_effect >>
  gvs[abi_decoder_address_frame_def, abi_decode_frame_def]
QED

Theorem abi_encoder_shared_array_exit_source:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  abi_encoder_member_phase_raw st final initial ready /\
  abi_decoder_address_frame owner_st.cs_next_var initial ready /\
  abi_encoder_shared_input (ei,ty,av) (owner_st,source,dst)
    (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix elem_ty avs k d initial.vs_memory ==>
  abi_encoder_shared_input (ei,ty,av) (owner_st,source,dst)
    (sb,source_cap) (d,sz) (first,last,b,cap) ready /\
  abi_encoder_array_prefix elem_ty avs k d ready.vs_memory
Proof
  strip_tac >> drule_all abi_encoder_array_exit_readonly >> strip_tac >>
  drule_all abi_encoder_shared_input_address >> simp[]
QED

(* Read-only exit assembly at the existing scalar sequence endpoint. *)
Theorem abi_encoder_shared_array_exit_run:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\
  (active ==> eval_operand dp initial = SOME (n2w slot) /\
    abi_decoder_operand_live st.cs_next_var dp /\ mload slot initial = n2w off /\
    slot < dimword (:256)) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w (32+if active then off else cnt*asz)) /\
    actual.vs_memory = initial.vs_memory /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func initial actual
Proof
  strip_tac >>
  `?actual. abi_encoder_member_phase_raw st final initial actual` by
    (Cases_on `active` >> gvs[]
     >- (drule_all abi_encode_array_dynamic_exit_sequence >> strip_tac >>
         qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
         gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def] >>
         goal_assum (drule_at Any) >> simp[]) >>
     drule_all abi_encode_array_static_exit_sequence >> strip_tac >>
     qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
     gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand out actual = SOME (n2w (32+if active then off else cnt*asz)) /\
   fresh_vars_wrt limit_st actual /\
   abi_decoder_address_frame st.cs_next_var initial actual /\
   actual.vs_current_bb = initial.vs_current_bb /\
   actual.vs_inst_idx = LENGTH final.cs_current_insts /\
   actual.vs_halted = initial.vs_halted` by
    (Cases_on `active` >> gvs[]
     >- (drule_all abi_encoder_array_dynamic_exit_raw_transport >> simp[]) >>
     drule_all abi_encoder_array_static_exit_raw_transport >> simp[]) >>
  drule_all abi_encoder_array_exit_readonly >> strip_tac >>
  drule_all abi_encoder_array_exit_effect >>
  disch_then (qspecl_then [`sz`,`lo`,`hi`,`d`,`ctx`] strip_assume_tac) >>
  `st.cs_current_bb = final.cs_current_bb` by
    (Cases_on `active` >> gvs[]
     >- (drule (CONJUNCT2 abi_encode_array_exit_shape) >> simp[]) >>
     drule (CONJUNCT1 abi_encode_array_exit_shape) >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_array_index_exit_run:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) st.cs_current_bb (LENGTH avs) origin initial /\
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ LENGTH st.cs_current_insts = 0 /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_array_index_exit_facts >> strip_tac >>
  drule abi_encoder_shared_array_index_facts >> strip_tac >>
  drule abi_encoder_shared_array_index_layout >> strip_tac >>
  qpat_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `sb < dimword (:256) /\ mload sb initial = n2w (LENGTH avs)` by
    (gvs[mem_word_at_eq_mload] >> decide_tac) >>
  `active ==> eval_operand dp initial = SOME (n2w cursor_slot) /\
    abi_decoder_operand_live st.cs_next_var dp /\
    mload cursor_slot initial = n2w (LENGTH (enc (Array NONE ty) (ListV avs))-32) /\
    cursor_slot < dimword (:256)` by
    (strip_tac >>
     `abi_encoder_cursor T dp cursor_site cursor_slot first site owner_st
       (LENGTH (enc (Array NONE ty) (ListV avs))-32) initial` by fs[] >>
     drule_all (Q.INST [`cursor_op` |-> `dp`] abi_encoder_cursor_bounds) >> strip_tac >>
     fs[abi_encoder_cursor_def, Excl "enc_def"] >>
     irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
   (active = F ==> LENGTH (enc (Array NONE ty) (ListV avs)) = 32+LENGTH avs*asz)` by
    (conj_tac >- decide_tac >> strip_tac >>
     `~is_dynamic ty` by metis_tac[] >>
     `!xs. SUM (MAP (abi_member_tail_size ty) xs) = 0` by
       (Induct >> simp[abi_member_tail_size_def]) >>
     fs[Excl "enc_def"]) >>
  `initial.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all abi_encoder_shared_array_exit_run >>
  disch_then (qspecl_then [`sz`,`lo`,`hi`,`d`,`ctx`] (qx_choose_then `actual` strip_assume_tac)) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  Cases_on `active` >> gvs[Excl "enc_def"]
QED

Theorem abi_encoder_shared_array_index_complete:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) st.cs_current_bb (LENGTH avs) origin initial /\
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ LENGTH st.cs_current_insts = 0 /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\ hi <= last /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap origin actual /\
    abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] origin actual /\
    (alloca_inv origin ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func origin actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_array_index_exit_run >>
  disch_then (qspec_then `site` (qx_choose_then `actual` strip_assume_tac)) >>
  drule abi_encoder_shared_array_index_facts >> strip_tac >>
  qpat_x_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap origin actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `initial` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] origin actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `initial` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func origin actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `initial` >> asm_rewrite_tac []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Concrete JMP entry: the generated header has no selected PHI. *)
Theorem abi_encoder_array_jump_extend_state:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras (jump_to label s) (jump_to label t)
Proof
  simp[abi_decoder_vars_extend_def, jump_to_def, vsr_frame_def,
    venom_state_component_equality, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_encoder_shared_array_loop_enter:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  mem_word_at d initial.vs_memory = n2w (LENGTH avs) /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) 0 initial (jump_to (FST labels) initial) /\
  abi_encoder_extend_sim ctx func initial (jump_to (FST labels) initial)
Proof
  strip_tac >> drule_all abi_encoder_array_loop_entry_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `abi_decoder_address_frame owner_st.cs_next_var initial (jump_to (FST labels) initial)` by
    simp[abi_decoder_address_frame_def, abi_decoder_operand_jump, jump_to_def] >>
  `fresh_vars_wrt limit_st (jump_to (FST labels) initial)` by simp[abi_decoder_fresh_jump] >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial
    (jump_to (FST labels) initial)` by (drule_all abi_scratch_address_effect >> simp[]) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) (jump_to (FST labels) initial)` by
    (drule_all abi_encoder_shared_input_address >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_shared_array_index_def] >>
  simp[abi_encoder_array_prefix_empty, abi_encoder_cursor_jump,
    abi_decoder_operand_jump, jump_to_def, abi_encoder_registered_effect_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED
