(* Counted bytes execution and semantic sequence share one endpoint. *)
Theory bodyPtrAbiEncodeBytesSemantic
Ancestors
  bodyPtrAbiEncodeBytesContract bodyPtrAbiEncodeSequenceEndpoint
  abiEncoderWindowBytes abiEncoderBytesCode abiEncoderWindowSequence abiEncoderInput abiEncoderMemory
  valueEncodingProps abiEncoder compileEnv emitHelper exprLoweringProps venomInst venomState venomExecSemantics
  ptrDiscipline words list rich_list arithmetic finite_map pred_set

Theorem abi_encode_bytes_length:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,en) ==>
  LENGTH (emitted_insts st en) = 10
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem abi_encode_bytes_semantic_contract_path:
  !total.
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) st = (out,en) /\
  abi_encoder_input (AbiBytestring maxlen) at (contractABI$BytesV bs) (w2n a) cap s.vs_memory /\
  (w2n a+cap <= w2n b \/ w2n b+(32+contractABI$ceil32 (LENGTH bs)) <= w2n a) /\
  not_fresh_at st dst /\ not_fresh_at st src /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  ptr_covers G tn dst s total /\ ptr_covers G tn src s (32+LENGTH bs) /\
  (!i. w2n a <= i /\ i < w2n a+(32+LENGTH bs) ==> i NOTIN tn.t_mem) /\
  LENGTH bs+31 < dimword(:256) /\ 32+LENGTH bs < dimword(:256) /\
  32+LENGTH bs <= total /\ contractABI$ceil32 (LENGTH bs)+32 <= total /\
  w2n b+contractABI$ceil32 (LENGTH bs) < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t H un u. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    lookup_var p t = SOME (n2w (LENGTH (enc at (contractABI$BytesV bs)))) /\
    op_taint un (Var p) = {} /\ not_fresh_at en p /\
    ptr_covers H un dst t total /\
    (!i. w2n b <= i /\ i < w2n b+LENGTH (enc at (contractABI$BytesV bs)) ==> i NOTIN un.t_mem) /\
    mem_bytes_at (w2n b) (LENGTH (enc at (contractABI$BytesV bs))) t.vs_memory =
      enc at (contractABI$BytesV bs) /\
    abi_decode_frame (w2n b) (LENGTH (enc at (contractABI$BytesV bs))) s t /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+10 /\
    (!q. not_fresh_at st q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint un (Var q) = op_taint tn (Var q)) /\
    mem_agree_outside
      {i | w2n b <= i /\ i < w2n b+(32+contractABI$ceil32 (LENGTH bs))}
      s.vs_memory t.vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b+(32+contractABI$ceil32 (LENGTH bs))) ==>
      (i IN un.t_mem <=> i IN tn.t_mem)) /\
    window_seq st en s u /\ t = u with vs_inst_idx := s.vs_inst_idx+10
Proof
  gen_tac >> strip_tac >>
  drule abi_encode_bytes_length >> strip_tac >>
  drule abi_encode_bytes_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st en)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  qabbrev_tac `cb = <|bb_label := s.vs_current_bb;
    bb_instructions := REPLICATE s.vs_inst_idx (mk_inst 0 ADD [] []) ++ emitted_insts st en|>` >>
  qabbrev_tac `cf = fn with fn_blocks := [cb]` >>
  `lookup_block s.vs_current_bb cf.fn_blocks = SOME cb /\
   isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx cb.bb_instructions)` by
    simp[Abbr `cb`, Abbr `cf`, lookup_block_def, FIND_thm, DROP_APPEND, LENGTH_REPLICATE] >>
  qpat_x_assum `lookup_block _ fn.fn_blocks = _` (mp_tac o GSYM) >>
  qpat_x_assum `isPREFIX _ (DROP _ bb.bb_instructions)` mp_tac >>
  Q.SUBGOAL_THEN `w2n a+cap <= w2n b \/ w2n b+(32+contractABI$ceil32 (LENGTH bs)) <= w2n a` assume_tac
  >- simp[] >>
  drule_at (Pat `lookup_block _ _ = _`) abi_encode_bytes_contract_path >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var dst s = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ dst s _`)) >>
  disch_then (qspecl_then [`limit_st`, `ctx`, `b`, `PG`, `D`, `total'`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rpt strip_tac >>
  `mload (w2n a) s = n2w (LENGTH bs)` by
    fs[abi_encoder_input_bytes_iff, mem_word_at_eq_mload] >>
  drule window_bytes_sequence >>
  disch_then (qspecl_then [`w2n a`, `s`, `w2n b`, `LENGTH bs`] mp_tac) >>
  (impl_tac >- (simp[eval_operand_def, w2n_lt] >> metis_tac[])) >> strip_tac >>
  `DROP s.vs_inst_idx cb.bb_instructions = emitted_insts st en /\
   LENGTH cb.bb_instructions = s.vs_inst_idx + LENGTH (emitted_insts st en)` by
    simp[Abbr `cb`, DROP_APPEND, LENGTH_REPLICATE] >>
  `t = t' with vs_inst_idx := s.vs_inst_idx+10` by
    (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) capped_sequence_endpoint >>
     simp[] >> disch_then irule >> fs[window_seq_def]) >>
  `EVERY (\b. EVERY (\i. i.inst_opcode <> REVERT) b.bb_instructions) cf.fn_blocks` by
    (qpat_x_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) _` mp_tac >>
     simp[Abbr `cf`, Abbr `cb`, EVERY_APPEND, EVERY_REPLICATE, mk_inst_def, EVERY_MEM] >>
     POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> gen_tac >> strip_tac >- simp[] >>
     first_x_assum drule >> strip_tac >>
     spose_not_then assume_tac >> gvs[is_terminator_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t)` by
    (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) capped_sequence_transport >>
     disch_then irule >> qexists_tac `bb` >> simp[]) >>
  qexistsl_tac [`p`, `t`, `H`, `un`, `t'`] >> simp[]
QED
