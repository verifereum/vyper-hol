(* Runtime control frames retained at the primitive encoder boundary. *)
Theory bodyPtrAbiEncodeFrames
Ancestors
  bodyPtrAbiEncodeWordChecks bodyPtrAbiEncodeCopyChecks abiEncoderLeafCode
  abiEncoderReentryLeaves abiEncoderLeaves abiEncoderAdmissible abiDecoderContract
  abiDecoderReentry emitHelperProps emitHelper compileEnv exprLoweringProps
  fragGasSeqPtr fragGasPathPtr venomExecSemantics venomState venomInst
  words list arithmetic

Theorem abi_encode_word_run_control[local]:
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord st = (out,en) /\
  lookup_var src s = SOME a /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> drule abi_encode_word_emitted_code >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      exec_read1_def, eval_operand_def] >>
  gvs[Once step_inst_base_def, exec_write2_def, eval_operand_def,
      update_var_def, lookup_var_def, AllCaseEqs(), mstore_def,
      write_memory_with_expansion_def]
QED

Theorem abi_encode_copy_run_control[local]:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy sz) st = (out,en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> drule abi_encode_copy_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      eval_operand_def, AllCaseEqs(), mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_word_checked_ptr_path_frame:
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord st = (out,en) /\
  eval_operand (Var src) s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  sb < dimword(:256) /\ db < dimword(:256) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  (!i. sb <= i /\ i < sb+32 ==> i NOTIN tn.t_mem) /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st en))) Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts st en))) /\
    eval_operand out t = SOME 32w /\
    mem_bytes_at db 32 t.vs_memory = mem_bytes_at sb 32 s.vs_memory /\
    fresh_vars_wrt limit_st t /\
    tnf.t_mem = tn.t_mem DIFF {i | db <= i /\ i < db+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at st p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    run_inst_seq (emitted_insts st en) s = OK t /\ abi_decode_frame db 32 s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  strip_tac >>
  `not_fresh_at st dst` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  `lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w db)` by
    fs[eval_operand_def] >>
  `!i. w2n (n2w sb:bytes32) <= i /\ i < w2n (n2w sb:bytes32)+32 ==>
    i NOTIN tn.t_mem` by simp[w2n_n2w] >>
  drule_all abi_encode_word_emitted_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all abi_encode_word_reentry >> strip_tac >>
  drule_all abi_encode_word_run_control >> strip_tac >>
  `abi_encoder_static_leaf AbiPrimWord` by simp[abi_encoder_static_leaf_def] >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `actual`] >> simp[w2n_n2w] >>
  once_rewrite_tac[ADD_COMM] >> irule run_inst_seq_gas_path_ptr >> metis_tac[]
QED

Theorem abi_encode_copy_checked_ptr_path_frame:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy sz) st = (out,en) /\
  eval_operand (Var src) s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w db) /\
  sb < dimword(:256) /\ db < dimword(:256) /\ sz < dimword(:256) /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  ~ctx_has_dalloca ctx /\
  (0 < sz ==> ptr_covers G tn src s sz /\ ptr_covers G tn dst s sz) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st en))) Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts st en))) /\
    eval_operand out t = SOME (n2w sz) /\
    mem_bytes_at db sz t.vs_memory = mem_bytes_at sb sz s.vs_memory /\
    fresh_vars_wrt limit_st t /\ Gf = G /\ tnf.t_var = tn.t_var /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_mem = (tn.t_mem DIFF {i | db <= i /\ i < db+sz}) UNION
      {db+i | i < sz /\ sb+i IN tn.t_mem} /\
    run_inst_seq (emitted_insts st en) s = OK t /\ abi_decode_frame db sz s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w db)` by
    fs[eval_operand_def] >>
  drule_all abi_encode_copy_emitted_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all abi_encode_copy_reentry >> strip_tac >>
  drule_all abi_encode_copy_run_control >> strip_tac >>
  `abi_encoder_static_leaf (AbiCopy sz)` by simp[abi_encoder_static_leaf_def] >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `actual`] >> simp[w2n_n2w] >>
  once_rewrite_tac[ADD_COMM] >> irule run_inst_seq_gas_path_ptr >> metis_tac[]
QED
