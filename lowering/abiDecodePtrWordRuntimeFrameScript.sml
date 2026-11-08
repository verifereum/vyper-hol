Theory abiDecodePtrWordRuntimeFrame
Ancestors
  abiDecodePtrBytesRuntimeFrame abiEncoder abiEncoderWindowLookup
  emitHelper emitHelperProps exprLoweringProps compileEnv freshWrites
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_word_memory_shape:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecPrimWord clamp) sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. (fresh_write_op i.inst_opcode \/
    MEM i.inst_opcode [MLOAD; MSTORE; MCOPY]) /\
    EVERY (not_fresh_at sb) i.inst_outputs) (emitted_insts sa sb)
Proof
  Cases_on `clamp` >>
  TRY (rename1 `IntClamp bits signed` >> Cases_on `signed`) >>
  Cases_on `base_op = Lit 0w` >>
  simp[Once compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_dec_addr_def, compile_abi_clamp_basetype_def,
       compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, fresh_write_op_def,
       not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_word_runtime_fresh:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecPrimWord clamp) sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ fresh_vars_wrt sa s ==>
  fresh_vars_wrt sb t
Proof
  strip_tac >> drule abi_decode_word_memory_shape >> strip_tac >>
  `fresh_vars_wrt sb s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[]) >>
  irule abi_window_seq_fresh >>
  qexistsl_tac [`sb`, `emitted_insts sa sb`, `s`] >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[MEM, fresh_write_op_simple]
QED
