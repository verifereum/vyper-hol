(* Ordinary allocation-free decoder execution on states with stale temporaries.
   Pruning is used only inside the checked sequence transfer, never as the
   caller's actual initial state. *)
Theory primitiveDecoderReentry
Ancestors
  abiDecoderReentryPointer abiDecoderReentry abiDecoderVarExtend abiDecoderVarSequence
  abiDecoderClampedWord abiDecoderBytes abiDecoderBytesFrame abiDecoderArrayInitReentry
  abiDecoderContract abiDecoderReservation abiEncoder emitHelperProps exprLoweringProps compileEnv
  venomState venomExecSemantics words arithmetic list

Theorem clamped_word_reentry_sequence:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi (DecPrimWord clamp) sa = ((),sb) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME sw /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decoder_clamp_valid clamp (abi_decode_load opc sw s) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var dst /\
  sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load opc sw s /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt limit t /\
    (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  `eval_operand src (abi_decoder_prune_vars sa.cs_next_var s) = SOME sw /\
    eval_operand dst (abi_decoder_prune_vars sa.cs_next_var s) = SOME (n2w d)` by
    simp[abi_decoder_prune_eval] >>
  `abi_decoder_clamp_valid clamp
    (abi_decode_load opc sw (abi_decoder_prune_vars sa.cs_next_var s))` by simp[] >>
  `fresh_vars_wrt sa (abi_decoder_prune_vars sa.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  drule_all abi_decoder_clamped_word_sequence >> strip_tac >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts sa sb)` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists `actual` >> gvs[abi_decoder_prune_vars_def]
QED

Theorem bytestring_sentinel_reentry_sequence:
  compile_abi_decode_to_buf dst src opc (Lit 0w) (Lit 0w) (DecBytestring n) sa = ((),sb) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME sw /\
  eval_operand dst s = SOME dw /\ abi_decode_load opc sw s = n2w cnt /\
  cnt <= n /\ n < dimword (:256) /\ abi_decode_bytes_copy_size n < dimword (:256) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var dst /\
  sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    mem_bytes_at (w2n dw) (abi_decode_bytes_copy_size n) t.vs_memory =
      mem_bytes_at (w2n sw) (abi_decode_bytes_copy_size n) (abi_decode_source opc s) /\
    abi_decode_frame (w2n dw) (abi_decode_bytes_copy_size n) s t /\
    fresh_vars_wrt limit t /\
    (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  `eval_operand src (abi_decoder_prune_vars sa.cs_next_var s) = SOME sw /\
    eval_operand dst (abi_decoder_prune_vars sa.cs_next_var s) = SOME dw` by
    simp[abi_decoder_prune_eval] >>
  `abi_decode_load opc sw (abi_decoder_prune_vars sa.cs_next_var s) = n2w cnt` by simp[] >>
  `fresh_vars_wrt sa (abi_decoder_prune_vars sa.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  drule_all abi_decode_bytes_sentinel_sequence >> strip_tac >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists `actual` >> gvs[abi_decoder_prune_vars_def]
QED
