(* Source-indexed bytes encoder base cases. *)
Theory extRetAbiSourceBytesCountedPtr
Ancestors
  extRetAbiBytesLivePtr abiEncoderSourceCorrect robustCopyTransportPtr
  exprLowering bodyPtrDefs loweringPosts vyperTyping valueEncoding
  ptrDiscipline venomState compileEnv words list finite_map pred_set arithmetic

Theorem compile_abi_encode_source_bytes_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (type_to_abi_enc_info fields ce (BaseT (BytesT (Dynamic N)))) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+LENGTH bs) /\
  ptr_covers G tn dst s (32+ceil32 (LENGTH bs)) /\
  32+LENGTH bs <= type_memory_size (BaseTV (BytesT (Dynamic N))) /\
  LENGTH bs <= dimword(:256)-32 /\ 32+ceil32 (LENGTH bs) < dimword(:256) /\
  w2n a+(32+LENGTH bs) < dimword(:256) /\
  w2n b+32+ceil32 (LENGTH bs) < dimword(:256) /\
  (w2n a+(32+LENGTH bs) <= w2n b \/ w2n b+32+ceil32 (LENGTH bs) <= w2n a) /\
  value_has_type (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) /\
  val_wf (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) /\ N < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) (w2n a) mem') ==>
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
      val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) (w2n a) mem')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring N)
      (vyper_to_abi_type env (BaseT (BytesT (Dynamic N)))) (contractABI$BytesV bs)
      (w2n a) (type_memory_size (BaseTV (BytesT (Dynamic N)))) mem'` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     drule_all abi_encoder_bytes_source_input >>
     simp[type_to_abi_enc_info_def]) >>
  rule_assum_tac (PURE_REWRITE_RULE [type_to_abi_enc_info_def]) >>
  drule_all compile_abi_encode_bytes_live_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)}`] >>
  simp[val_footprint_def] >> conj_tac
  >- (qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
      simp[mem_agree_outside_def] >> metis_tac[]) >>
  fs[]
QED

Theorem compile_abi_encode_source_string_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (type_to_abi_enc_info fields ce (BaseT (StringT N))) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+LENGTH text) /\
  ptr_covers G tn dst s (32+ceil32 (LENGTH text)) /\
  32+LENGTH text <= type_memory_size (BaseTV (StringT N)) /\
  LENGTH text <= dimword(:256)-32 /\ 32+ceil32 (LENGTH text) < dimword(:256) /\
  w2n a+(32+LENGTH text) < dimword(:256) /\
  w2n b+32+ceil32 (LENGTH text) < dimword(:256) /\
  (w2n a+(32+LENGTH text) <= w2n b \/ w2n b+32+ceil32 (LENGTH text) <= w2n a) /\
  value_has_type (BaseTV (StringT N)) (StringV text) /\
  val_wf (BaseTV (StringT N)) (StringV text) /\ N < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (BaseTV (StringT N)) (StringV text) (w2n a) mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+ceil32 (LENGTH text))) /\ op_taint tnf out = {} /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (32+LENGTH text)
      (mstore (w2n b+ceil32 (LENGTH text)) 0w s)).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH text)} /\
    (!i. w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH text) ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH text)}
      sf.vs_memory s.vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH text)) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf dst sf (32+ceil32 (LENGTH text)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (BaseTV (StringT N)) (StringV text) (w2n a) mem')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring N)
      (vyper_to_abi_type env (BaseT (StringT N)))
      (contractABI$BytesV (MAP (n2w o ORD) text))
      (w2n a) (type_memory_size (BaseTV (StringT N))) mem'` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     drule_all abi_encoder_string_source_input >> simp[type_to_abi_enc_info_def]) >>
  rule_assum_tac (PURE_REWRITE_RULE [type_to_abi_enc_info_def]) >>
  drule_all (PURE_REWRITE_RULE [LENGTH_MAP]
    (Q.INST [`bs` |-> `MAP (n2w o ORD) text`]
      (SPEC_ALL compile_abi_encode_bytes_live_ambient_counted_ptr))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH text)}`] >>
  simp[val_footprint_def] >> conj_tac
  >- (qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
      simp[mem_agree_outside_def] >> metis_tac[]) >>
  fs[]
QED
