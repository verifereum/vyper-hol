(* ABI bytes input observes only its length header and live payload. *)
Theory extRetAbiBytesLivePtr
Ancestors
  extRetAbiBytesCountedPtr abiEncoderInput bodyPtrDefs ptrDiscipline
  venomState compileEnv exprLowering words list arithmetic

Theorem abi_encoder_input_bytes_live_capacity:
  32+LENGTH bs <= cap ==>
  (abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem <=>
   abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a (32+LENGTH bs) mem)
Proof
  simp[abi_encoder_input_bytes_iff]
QED

Theorem abi_encoder_input_bytes_robust_live:
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem') ==>
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a (32+LENGTH bs) mem')
Proof
  simp[abi_encoder_input_bytes_iff] >> metis_tac[]
QED

Theorem compile_abi_encode_bytes_live_ambient_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+LENGTH bs) /\
  ptr_covers G tn dst s (32+ceil32 (LENGTH bs)) /\
  32+LENGTH bs <= cap /\ LENGTH bs <= dimword(:256)-32 /\
  32+ceil32 (LENGTH bs) < dimword(:256) /\
  w2n a+(32+LENGTH bs) < dimword(:256) /\
  w2n b+32+ceil32 (LENGTH bs) < dimword(:256) /\
  (w2n a+(32+LENGTH bs) <= w2n b \/ w2n b+32+ceil32 (LENGTH bs) <= w2n a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+ceil32 (LENGTH bs))) /\ op_taint tnf out = {} /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (32+LENGTH bs)
      (mstore (w2n b+ceil32 (LENGTH bs)) 0w s)).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)} /\
    (!i. w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs) ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)}
      sf.vs_memory s.vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf dst sf (32+ceil32 (LENGTH bs)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_encoder_input_bytes_robust_live >> strip_tac >>
  `32+LENGTH bs <= 32+LENGTH bs` by simp[] >>
  drule_all compile_abi_encode_bytes_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule abi_encoder_input_capacity >>
  qexists_tac `32+LENGTH bs` >> asm_rewrite_tac[] >>
  first_x_assum irule >> asm_rewrite_tac[]
QED
