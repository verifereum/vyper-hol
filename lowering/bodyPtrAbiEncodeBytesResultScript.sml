(* Semantic bytes/string result on the independently checked counted path. *)
Theory bodyPtrAbiEncodeBytesResult
Ancestors
  bodyPtrAbiEncodeBytesPhases bodyPtrAbiEncodeBytesMemory
  abiEncoderInput abiEncoderBytes abiEncoderRounding
  valueEncodingProps bodyPtrDefs bodyPtrAbiEncodeCursorFrame
  compileEnv exprLoweringProps emitHelperProps venomState venomExecSemantics
  ptrDiscipline words arithmetic

Theorem abi_encode_bytes_result_path:
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
  ?p t H un. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    lookup_var p t = SOME (n2w (LENGTH (enc at (contractABI$BytesV bs)))) /\
    op_taint un (Var p) = {} /\ not_fresh_at en p /\
    ptr_covers H un dst t total /\
    (!i. w2n b <= i /\ i < w2n b+LENGTH (enc at (contractABI$BytesV bs)) ==> i NOTIN un.t_mem) /\
    mem_bytes_at (w2n b) (LENGTH (enc at (contractABI$BytesV bs))) t.vs_memory =
      enc at (contractABI$BytesV bs) /\
    abi_decode_frame (w2n b) (LENGTH (enc at (contractABI$BytesV bs))) s t /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+10
Proof
  gen_tac >> strip_tac >>
  `mload (w2n a) s = n2w (LENGTH bs) /\ 32+LENGTH bs <= cap /\
   (at = Bytes NONE \/ at = String)` by
    (fs[abi_encoder_input_bytes_iff, mem_word_at_eq_mload]) >>
  drule_all abi_encode_bytes_checked_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `w2n a+(32+LENGTH bs) <= w2n b \/
   w2n b+(32+contractABI$ceil32 (LENGTH bs)) <= w2n a` by decide_tac >>
  qpat_assum `abi_encode_read_frame st _ G _ t H un`
    (mp_then Any mp_tac abi_encode_bytes_memory_result) >>
  disch_then (qspecl_then [`maxlen`, `cap`, `at`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH (enc at (contractABI$BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_bytes_encoding] >>
  qexistsl_tac [`p`, `t`, `H`, `un`] >> asm_rewrite_tac []
QED
