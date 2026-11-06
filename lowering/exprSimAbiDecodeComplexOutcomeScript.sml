(* Reentry-safe guard and owned heterogeneous constructor integration. *)
Theory exprSimAbiDecodeComplexOutcome
Ancestors
  exprSimAbiDecodeAbortReentry exprSimAbiDecodeCompositePrefix
  exprSimAbiDecodeTupleTraversal exprSimAbiDecodeOwnedMember
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderReentry abiDecoderVarExtend
  abiDecoderSequenceReach abiDecoderFiniteControl
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst words list rich_list arithmetic

Theorem abi_decode_complex_guard_abort_opcodes[local]:
  abi_decode_complex_head_guard src hi k st = ((),st') ==>
  EVERY (\i. MEM i.inst_opcode [ADD; LT; GT; AND; ISZERO; MLOAD; ASSERT])
    (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_decode_complex_head_guard_revert_reentry:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME(n2w p) /\
  eval_operand hi s = SOME(n2w H) /\
  p < dimword(:256) /\ k < dimword(:256) /\ H < dimword(:256) /\
  H < p+k /\ abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w p) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w H)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  drule_all abi_decode_complex_head_guard_revert >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  drule abi_decode_complex_guard_abort_opcodes >> strip_tac >>
  drule_all abi_decode_guard_sequence_vars_extend_abort >> simp[]
QED

Theorem abi_decode_complex_head_guard_abort_reentry:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME(n2w p) /\
  eval_operand hi s = SOME(n2w H) /\
  p < dimword(:256) /\ k < dimword(:256) /\ H < dimword(:256) /\
  H < p+k /\ abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. Dabort ctx fn s Revert_abort u
Proof
  strip_tac >> drule_all abi_decode_complex_head_guard_revert_reentry >> strip_tac >>
  drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  simp[Dabort_def] >> qexistsl_tac [`t with vs_inst_idx := n`, `0`] >> simp[]
QED
