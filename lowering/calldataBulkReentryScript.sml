(* Allocation-free bulk execution with reusable temporary names. *)
Theory calldataBulkReentry
Ancestors
  abiDecoderBulk abiDecoderBulkExecute abiDecoderReentryPointer abiDecoderReentry
  abiDecoderVarExtend abiDecoderVarSequence abiDecoderBytesFrame
  abiDecoderContract abiDecoderComposition abiDecoderFrameCompose abiDecoderReservation
  compileEnv venomState venomExecSemantics exprLoweringProps abiEncoder
  list words arithmetic abiDecoderArrayInitReentry

Theorem calldata_bulk_reentry_sequence:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) sa = ((),sb) /\
  ~dec_info_needs_clamp ei /\
  eval_operand src s = SOME (n2w pos) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load CALLDATALOAD (n2w pos : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  pos + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var dst /\
  sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (pos + 32) (n * mem_sz) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (32 + n * mem_sz) s t /\ fresh_vars_wrt limit t /\
    (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  `eval_operand src (abi_decoder_prune_vars sa.cs_next_var s) = SOME (n2w pos) /\
   eval_operand dst (abi_decoder_prune_vars sa.cs_next_var s) = SOME (n2w d) /\
   eval_operand (Lit 0w) (abi_decoder_prune_vars sa.cs_next_var s) = SOME (n2w 0)` by
    simp[abi_decoder_prune_eval, eval_operand_def] >>
  `abi_decode_load CALLDATALOAD (n2w (0 + pos) : bytes32)
      (abi_decoder_prune_vars sa.cs_next_var s) = n2w n` by simp[] >>
  `fresh_vars_wrt sa (abi_decoder_prune_vars sa.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `?clean.
    run_inst_seq (emitted_insts sa sb) (abi_decoder_prune_vars sa.cs_next_var s) = OK clean /\
    mem_word_at d clean.vs_memory = n2w n /\
    mem_bytes_at (d+32) (n*mem_sz) clean.vs_memory =
      mem_bytes_at (pos+32) (n*mem_sz)
        (abi_decode_source CALLDATALOAD (abi_decoder_prune_vars sa.cs_next_var s)) /\
    abi_decode_frame d (32+n*mem_sz) (abi_decoder_prune_vars sa.cs_next_var s) clean /\
    fresh_vars_wrt sb clean /\
    (!op w. eval_operand op (abi_decoder_prune_vars sa.cs_next_var s) = SOME w ==>
      eval_operand op clean = SOME w) /\ inst_extends sa sb` by
    (irule (SRULE [] (Q.INST [`src_base` |-> `0`] abi_decode_bulk_sequence)) >>
     simp[] >> metis_tac[]) >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts sa sb)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists `actual` >> gvs[abi_decoder_prune_vars_def, abi_decode_source_def]
QED
