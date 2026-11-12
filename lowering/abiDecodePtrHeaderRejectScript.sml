Theory abiDecodePtrHeaderReject
Ancestors
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  abiDecoderReentry abiDecoderContract emitHelperProps exprLoweringProps
  context compileEnv emitHelper fragExec venomExecSemantics venomState
  venomInst words list rich_list arithmetic

Theorem abi_builtin_decode_header_reject_run:
  abi_builtin_decode_header data mn mx sa = ((len,src),sh) /\
  eval_operand data s = SOME w /\ mload (w2n w) s = n2w cnt /\
  abi_decoder_operand_live sa.cs_next_var data /\ ~s.vs_halted /\
  cnt < dimword(:256) /\ mn < dimword(:256) /\ mx < dimword(:256) /\
  (cnt < mn \/ mx < cnt) ==>
  ?u. run_inst_seq (emitted_insts sa sh) s = Abort Revert_abort u
Proof
  Cases_on `mn = mx` >>
  simp[abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  `data <> Var (STRING #"%" (toString sa.cs_next_var))` by
    (Cases_on `data` >> gvs[abi_decoder_operand_live_def,
      abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_REFL]) >>
  `eval_operand data (update_var (STRING #"%" (toString sa.cs_next_var))
     (n2w cnt) s) = SOME w` by
    (Cases_on `data` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_read1_def, exec_pure2_def] >>
  simp[eval_operand_def, lookup_var_update_var, fresh_var_distinct,
    exec_pure1_def, w2n_n2w] >>
  Cases_on `cnt < mn` >> Cases_on `mx < cnt` >>
  simp[bool_to_word_def, WORD_AND_CLAUSES]
QED
