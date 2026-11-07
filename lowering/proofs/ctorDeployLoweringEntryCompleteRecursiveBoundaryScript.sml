Theory ctorDeployLoweringEntryCompleteRecursiveBoundary
Ancestors
 ctorDeployLoweringEntryCompleteScalar ctorDeployLoweringEntryArrayRun
 ctorAbiActualArrayBody ctorAbiActualFrame ctorAbiActualWorld
 ctorAbiActualArrayIteration ctorDeployLoweringEntryRegistration
 abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs abiDecoderContract
 abiDecoderReentry abiDecoderVarSequence abiDecoderArraySetupCode
 abiDecoderLoop fragExec instIdxIndep compileEnv venomExecSemantics venomState
 abiDecoderTypedContract abiEncoderRegisteredEffect valueEncoding words list
 finite_map venomMemDefs

Theorem deploy_ctor_array_setup_complete_sim:
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
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
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
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all ctor_actual_array_setup_labels >> strip_tac >>
  drule ctor_actual_array_setup_opcodes >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def,
    abi_encoder_registered_effect_def]
QED
