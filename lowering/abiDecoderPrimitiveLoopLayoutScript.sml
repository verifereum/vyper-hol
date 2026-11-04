(* Derive loop-code containment from the actual emitted compiler states. *)
Theory abiDecoderPrimitiveLoopLayout
Ancestors
  abiDecoderLoopEmit abiDecoderPrimitiveLoopContext abiDecoderPrimitiveLoopInvariant
  abiDecoderPrimitiveLoopFragment abiDecoderStaticLoopSetup abiDecoderClampedWord
  abiDecoderDynamic abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderExecution
  abiDecoderContract fragExec exprLoweringProps emitHelperProps emitHelper compileEnv
  venomExecSemantics venomInst words list rich_list arithmetic

Theorem abi_decoder_primitive_setup_head:
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\ st.cs_current_insts = [] ==>
  FST ops = Var (STRING #"%" (toString st.cs_next_var)) /\
  ?rest. middle.cs_current_insts =
    mk_inst st.cs_next_id MLOAD [ip] [STRING #"%" (toString st.cs_next_var)] :: rest
Proof
  simp[abi_decode_array_element_setup_def, abi_decoder_dynamic_def,
       abiEncoderTheory.dec_info_needs_offset_def,
       abi_decode_indexed_address_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem abi_decoder_primitive_body_phi:
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st1) /\ st.cs_current_insts = [] /\ abi_decode_source_opcode opc ==>
  FST ops = Var (STRING #"%" (toString st.cs_next_var)) /\
  phi_prefix_length (st1.cs_current_insts ++ tail) = 0
Proof
  strip_tac >> drule_all abi_decoder_primitive_setup_head >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  fs[IS_PREFIX_APPEND] >> simp[phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decoder_primitive_loop_layout:
  abi_decode_loop_prefix ip src opc start = (labels,st0) /\
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),end_st) /\
  fn_has_code start end_st fn /\ abi_decode_source_opcode opc /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    (FST labels) (SND (SND labels)) (start.cs_next_id + 1) start.cs_next_var
    (STRING #"%" (toString st0.cs_next_var)) end_st
Proof
  strip_tac >>
  `st0.cs_current_insts = [] /\ start.cs_next_var + 4 <= st0.cs_next_var`
    by (gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def]) >>
  drule_all abi_decoder_primitive_body_phi >>
  disch_then (qspec_then `abi_decode_backedge_insts st1.cs_next_id
    (STRING #"%" (toString st0.cs_next_var)) (STRING #"%" (toString st1.cs_next_var))
    ip (FST (labels:string # string # string))` strip_assume_tac) >>
  drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >>
  gvs[abi_decoder_primitive_loop_compiled_def, abi_decoder_primitive_loop_code_def,
     abi_decode_loop_cfg_def, abi_decode_loop_prefix_state_def,
     abi_decode_loop_suffix_state_def, fn_has_code_def, emitted_blocks_def,
     fresh_label_output_def, DISJ_IMP_THM, FORALL_AND_THM] >> simp[]
QED
