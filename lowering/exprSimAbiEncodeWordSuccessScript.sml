Theory exprSimAbiEncodeWordSuccess
Ancestors
  exprSimAbiEncodeStagedObserver exprSimAbiEncodePrefixWindow
  abiBuiltinEncodeWord abiBuiltinAllocation exprSimHash abiDecoderGuards context emitHelper emitHelperProps
  exprLoweringProps compileEnv venomState venomInst list rich_list
  abiBuiltinEncodeCode abiCopyExecution abiEncoder

Theorem abi_encode_word_staging_path:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  fn_has_code sa sh func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm) s = OK allocated /\
  run_inst_seq (emitted_insts sm sh) allocated = OK staged ==>
  gas_marked_path F ctx func s 0
    (OK (staged with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
  ~staged.vs_halted /\ staged.vs_current_bb = sh.cs_current_bb
Proof
  strip_tac >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `inst_extends sm sh` by metis_tac[inst_extends_emit_void] >>
  `inst_extends sa sm` by metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa sh) s = OK staged` by
    (irule run_inst_seq_compose_ok >>
     qexistsl_tac [`allocated`, `sm`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh` by
    (fs[inst_extends_def]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sh)) = 0` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     fs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC, mk_inst_def]) >>
  drule_all hash_run_path >> disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

Theorem abi_encode_word_encoder_no_blocks:
  is_word_type ty /\
  lower_abi_encode ensure mid src (type_to_abi_enc_info sf ce ty) maxlen st = (out,final) ==>
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb
Proof
  strip_tac >>
  `type_to_abi_enc_info sf ce ty = AbiCopy 32` by
    (irule (cj 2 abi_builtin_encode_word_info) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `lower_abi_encode _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >> strip_tac >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[compile_abi_copy_shape, compile_copy_memory_dynamic_def,
    emit_void_def, emit_def, fresh_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[]
QED
