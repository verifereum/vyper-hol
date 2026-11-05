(* Conditional counted paths for the actual primitive encoder runs.
   Pointer checks remain explicit: these boundaries do not infer safety
   from the encoder's semantic continuation simulation. *)
Theory bodyPtrAbiEncodePrimitive
Ancestors
  abiEncoderReentryLeaves abiEncoderLeafCode abiEncoderAdmissible
  fragGasSeqPtr fragGasPathPtr

Theorem abi_encode_word_reentry_ptr_path:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts st st') s G' tn' ==>
  ?t.
    gas_path_ptr D lo ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
      G' tn' (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    eval_operand out t = SOME 32w /\
    mem_bytes_at db 32 t.vs_memory = mem_bytes_at sb 32 s.vs_memory /\
    fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule_all abi_encode_word_reentry >> strip_tac >>
  `abi_encoder_static_leaf AbiPrimWord` by simp[abi_encoder_static_leaf_def] >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  qexists_tac `actual` >> asm_rewrite_tac[] >>
  irule run_inst_seq_gas_path_ptr >> metis_tac[]
QED

Theorem abi_encode_copy_reentry_ptr_path:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts st st') s G' tn' ==>
  ?t.
    gas_path_ptr D lo ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
      G' tn' (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    eval_operand out t = SOME (n2w sz) /\
    mem_bytes_at db sz t.vs_memory = mem_bytes_at sb sz s.vs_memory /\
    fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule_all abi_encode_copy_reentry >> strip_tac >>
  `abi_encoder_static_leaf (AbiCopy sz)` by simp[abi_encoder_static_leaf_def] >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  qexists_tac `actual` >> asm_rewrite_tac[] >>
  irule run_inst_seq_gas_path_ptr >> metis_tac[]
QED
