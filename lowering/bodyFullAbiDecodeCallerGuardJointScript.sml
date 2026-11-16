(* The pre-allocation length guard, with one endpoint for all observers. *)
Theory bodyFullAbiDecodeCallerGuardJoint
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeCallerHeaderGuard
  bodyFullAbiDecodeClampMemory bodyFullAbiDecodeLeafCases
  bodyFullAbiDecodeFiniteGuard bodyFullAbiDecodeFiniteObserved
  bodyFullBopWordSuccess
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  exprSimAbiDecodeBuiltinHeader exprSimAbiDecodeFreshProbe
  abiDecoderAbortReentry abiDecoderVarSequence abiDecoderVarExtend abiDecoderReentry
  abiDecoderReentryPointer abiBuiltinPrefix
  emitHelperProps exprLoweringProps compileEnv emitHelper freshWrites
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome bodyPtrBopScalarDynamic
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPathMem fragGasPath
  venomExecSemantics venomState venomInst words list rich_list pred_set

Theorem abi_decode_caller_guard_reentry[local]:
  abi_builtin_length_guard len mn mx sa = ((),sb) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)
Proof
  Cases_on `mn = mx` >>
  simp[abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
    abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_caller_guard_runtime[local]:
  abi_builtin_length_guard len mn mx sa = ((),sb) /\
  eval_operand len u = SOME (n2w cnt) /\
  mn <= mx /\ mx < dimword (:256) /\ cnt < dimword (:256) /\
  abi_decoder_operand_live sa.cs_next_var len ==>
  ((mn <= cnt /\ cnt <= mx) ==>
     ?v. run_inst_seq (emitted_insts sa sb) u = OK v) /\
  (~(mn <= cnt /\ cnt <= mx) ==>
     ?v. run_inst_seq (emitted_insts sa sb) u = Abort Revert_abort v)
Proof
  strip_tac >> drule abi_builtin_length_guard_shape >> strip_tac >>
  `fresh_vars_wrt sb (abi_decoder_prune_vars sa.cs_next_var u)` by
    (irule abi_decode_pruned_limit_fresh >> simp[]) >>
  `eval_operand len (abi_decoder_prune_vars sa.cs_next_var u) = SOME (n2w cnt)` by
    simp[abi_decoder_prune_eval] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)` by
    metis_tac[abi_decode_caller_guard_reentry] >>
  `abi_decoder_vars_extend u.vs_vars (abi_decoder_prune_vars sa.cs_next_var u) u` by
    irule abi_decoder_prune_extension >>
  `sb.cs_next_var <= sb.cs_next_var` by simp[] >>
  conj_tac
  >- (strip_tac >> drule_all abi_builtin_length_guard >> strip_tac >>
      gvs[abi_builtin_prefix_def] >>
      drule_all abi_decoder_sequence_vars_extend >> metis_tac[]) >>
  strip_tac >> `mn < dimword (:256)` by decide_tac >>
  drule_all abi_decode_builtin_length_guard_revert >> strip_tac >>
  metis_tac[abi_decoder_sequence_revert_reentry]
QED
