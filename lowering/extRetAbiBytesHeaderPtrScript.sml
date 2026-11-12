(* The actual bytes encoder header load, with a semantic robust input. *)
Theory extRetAbiBytesHeaderPtr
Ancestors
  extRetBytesCopyCountedPtr extRetAbiReadCleanPtr extRetAbiReadBoundsPtr
  abiEncoderInput bodyPtrDefs compileEnv emitHelper venomState venomInst
  valueEncoding words finite_map ptrDiscipline

Theorem abi_encoder_bytes_header_ambient_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s cap /\
  lookup_var src s = SOME a /\ not_fresh_at sa src /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (LENGTH bs)) /\ op_taint tnf (Var out) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf src sf cap /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem')
Proof
  strip_tac >>
  `abi_encoder_input (AbiBytestring maxlen) at (BytesV bs)
     (w2n a) cap s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `32 <= cap /\ mem_word_at (w2n a) s.vs_memory = n2w (LENGTH bs)` by
    (gvs[abi_encoder_input_bytes_iff]) >>
  `abi_encoder_read_window (AbiBytestring maxlen) (BytesV bs) (w2n a) (w2n a) 32` by
    simp[abi_encoder_read_window_rules] >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[abi_encoder_read_window_clean] >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  gvs[mload_def, mem_word_at_def] >>
  gvs[ptr_covers_def] >> metis_tac[]
QED

Theorem abi_encoder_bytes_header_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s cap /\
  lookup_var src s = SOME a /\ not_fresh_at sa src /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (LENGTH bs)) /\ op_taint tnf (Var out) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf src sf cap /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem')
Proof
  strip_tac >> drule_all abi_encoder_bytes_header_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED
