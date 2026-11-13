(* Counted memory-safe rejection of the builtin's source-length guard. *)
Theory abiDecodeMemHeaderReject
Ancestors
  abiDecodeMemHeader exprSimAbiDecodeBuiltinHeader
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  abiDecoderContract emitHelperProps exprLoweringProps compileEnv emitHelper
  fragExecMem fragGasMode bodyUnopFragMemory entrySinkExtraction entryDecoderHistoryFrame
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decode_header_no_gas[local]:
  abi_builtin_decode_header data lo hi st = (inputs,last) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts st last)
Proof
  Cases_on `lo = hi` >>
  simp[abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def,
    abi_builtin_bound_test_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_decode_header_reject_path_mem:
  abi_builtin_decode_header data lo hi st = (inputs,last) /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  w2n p + 32 <= s.vs_alloca_next /\
  lo < dimword (:256) /\ hi < dimword (:256) /\ cnt < dimword (:256) /\
  ~(lo <= cnt /\ cnt <= hi) /\
  abi_decoder_operand_live st.cs_next_var data /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >> drule_all abi_decode_builtin_header_revert >> strip_tac >>
  drule_all abi_decode_header_mem_ok >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_decode_header_no_gas >> strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st last) (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st last)`
    by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
