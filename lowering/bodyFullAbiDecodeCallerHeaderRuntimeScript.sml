(* Finite header execution with arbitrary pre-existing temporary bindings. *)
Theory bodyFullAbiDecodeCallerHeaderRuntime
Ancestors
  abiBuiltinDecodeHeader exprSimAbiDecodeBuiltinHeader abiDecoderAbortReentry
  abiDecoderVarSequence abiDecoderVarExtend abiDecoderReentry
  abiDecoderReentryPointer exprSimAbiDecodeFreshProbe
  abiBuiltinPrefix abiBuiltinLengthGuard abiBuiltinBoundTests
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decode_caller_header_reentry_code[local]:
  abi_builtin_decode_header data mn mx st = (inputs,last) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st last)
Proof
  Cases_on `mn = mx` >>
  simp[abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_caller_header_runtime:
  abi_builtin_decode_header data mn mx st = (inputs,last) /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  mn <= mx /\ mx < dimword (:256) /\ cnt < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data ==>
  ((mn <= cnt /\ cnt <= mx) ==>
    ?t. run_inst_seq (emitted_insts st last) s = OK t /\
      eval_operand (FST inputs) t = SOME (n2w cnt) /\
      eval_operand (SND inputs) t = SOME (p+32w)) /\
  (~(mn <= cnt /\ cnt <= mx) ==>
    ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t)
Proof
  strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  `fresh_vars_wrt last (abi_decoder_prune_vars st.cs_next_var s)` by
    (irule abi_decode_pruned_limit_fresh >> simp[]) >>
  `eval_operand data (abi_decoder_prune_vars st.cs_next_var s) = SOME p` by
    simp[abi_decoder_prune_eval] >>
  `mload (w2n p) (abi_decoder_prune_vars st.cs_next_var s) = n2w cnt` by
    simp[abi_decoder_prune_vars_def, mload_def] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st last)` by
    metis_tac[abi_decode_caller_header_reentry_code] >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  conj_tac
  >- (strip_tac >>
      `last.cs_next_var <= last.cs_next_var` by simp[] >>
      drule_all abi_builtin_decode_header >> strip_tac >>
      gvs[abi_builtin_prefix_def] >>
      drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
      metis_tac[abi_decoder_vars_extend_eval]) >>
  strip_tac >>
  `mn < dimword (:256)` by decide_tac >>
  `last.cs_next_var <= last.cs_next_var` by simp[] >>
  drule_all abi_decode_builtin_header_revert >> strip_tac >>
  metis_tac[abi_decoder_sequence_revert_reentry]
QED
