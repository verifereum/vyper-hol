(* Exact entry-live operand frame for the MLOAD array header. *)
Theory abiDecodeMemArrayHeaderFrame
Ancestors
  abiDecoderArrayHeader abiDecoderArrayLoopInit abiDecoderReentry abiDecoderContract
  appendStorageStageTransportPtr stmtReasonMemory
  emitHelperProps exprLoweringProps compileEnv emitHelper venomExecSemantics
  venomState venomInst list rich_list pred_set

Theorem abi_decode_array_header_live_frame:
  abi_decode_array_header dst addr MLOAD st = (cnt,st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  !op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op (t with vs_inst_idx := j) = eval_operand op s
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_data_section >> strip_tac >>
  Cases >> simp[abi_decoder_operand_live_def, eval_operand_def] >> strip_tac >>
  rename1 `x IN abi_decoder_older_vars st.cs_next_var` >>
  `lookup_var x t = lookup_var x s` suffices_by
    simp[lookup_var_def] >>
  irule run_inst_seq_non_output_vars >>
  qexists_tac `emitted_insts st st'` >> simp[] >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
  fs[abi_decoder_older_vars_def]
QED
