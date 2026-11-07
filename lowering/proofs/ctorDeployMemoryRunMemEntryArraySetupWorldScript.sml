Theory ctorDeployMemoryRunMemEntryArraySetupWorld
Ancestors
  ctorDeployMemoryRunMemEntryArrayBody ctorDeployMemoryRunMemEntryArraySteps
  ctorDeployMemoryRunMemEntrySequenceWorld
  ctorAbiActualArrayBody ctorAbiActualFrame ctorAbiActualWorld
  abiDecoderArraySetupCode abiDecoderArraySetupInputs abiDecoderCoherence
  abiDecoderContract abiDecodeRanges abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderVarSequence abiDecoderLoop abiDecoderArrayInvariant
  abiEncoderRegisteredEffect abiEncoderProps abiEncoder contractABI
  compileEnv context emitHelperProps instIdxIndep fragExec
  venomInst venomExecSemantics venomState venomMemDefs
  list rich_list words arithmetic
  ctorAbiActualArrayIteration abiDecoderLoopSetup abiDecoderIndexedAddress
  emitHelper exprLoweringProps entrySinkExtraction
  ctorDeployMemoryRunMemEntryCompositeSetup

Theorem ctor_checked_array_setup_world_labels:
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) s.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post))) <= LENGTH s.vs_data_section /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w (LENGTH pre)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [] s t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    gas_path_mem ctx func s 0 (OK t) /\ t.vs_gas_readings = s.vs_gas_readings /\
    alloca_history func t /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_outcomes = s.vs_outcomes
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `mload (w2n (n2w slot : bytes32)) s = n2w (LENGTH pre)` by simp[] >>
  drule_all ctor_actual_array_setup_labels >> strip_tac >>
  drule ctor_actual_array_setup_opcodes >> strip_tac >>
  drule_all ctor_decoder_sequence_context_world >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` >>
     Cases_on `hi = Lit 0w` >>
     simp[abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
       compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, emitted_insts_def] >>
     strip_tac >> gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  drule_all ctor_checked_array_setup_mem_ok >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `t.vs_allocas = s.vs_allocas` by fs[abi_decoder_address_frame_def] >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
      fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem ctor_checked_array_setup_world_at_index:
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV avs))) s.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV avs)) <= LENGTH s.vs_data_section /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) avs j)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + j * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [] s t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    gas_path_mem ctx func s 0 (OK t) /\ t.vs_gas_readings = s.vs_gas_readings /\
    alloca_history func t /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_outcomes = s.vs_outcomes
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  mp_tac (Q.INST [`pre` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `post` |-> `DROP (SUC j) (avs:abi_value list)`,
    `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`]
    ctor_checked_array_setup_world_labels) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED
