(* Explicit bytes instance of the recursive encoder resource interface. *)
Theory bodyPtrAbiEncodeBytesContract
Ancestors
  bodyPtrAbiEncodeBytesPhases bodyPtrAbiEncodeBytesMemory
  bodyPtrAbiEncodeRecursiveFrame bodyPtrAbiEncodeCursorFrame bodyPtrDefs
  abiEncoderMemory abiDecoderContract abiEncoderRounding abiEncoderInput abiEncoderBytes
  valueEncodingProps
  compileEnv exprLoweringProps emitHelperProps venomState venomExecSemantics
  ptrDiscipline words arithmetic finite_map pred_set

Theorem abi_encode_bytes_frame_projection:
  abi_encode_read_frame st
    (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s)) G
    (tn with t_mem := tn.t_mem DIFF {i | db+rounded <= i /\ i < db+rounded+32}
       DIFF {i | db <= i /\ i < db+(32+cnt)}) t H un /\
  cnt <= rounded ==>
  (!q. not_fresh_at st q ==>
    lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
    op_taint un (Var q) = op_taint tn (Var q)) /\
  mem_agree_outside {i | db <= i /\ i < db+(32+rounded)} s.vs_memory t.vs_memory /\
  (!i. ~(db <= i /\ i < db+(32+rounded)) ==> (i IN un.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `abi_decode_frame db (32+rounded) s
    (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s))` by
    (irule abi_encoder_bytes_write_frame >> simp[]) >>
  qpat_x_assum `abi_encode_read_frame _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_encode_read_frame_def] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `!q. not_fresh_at st q ==> _` mp_tac >>
      simp_tac (srw_ss()) [mcopy_def, mstore_def, write_memory_with_expansion_def,
        lookup_var_def, op_taint_def, LET_THM]) >>
  conj_tac
  >- (simp_tac (srw_ss()) [mem_agree_outside_def] >> rpt strip_tac >>
      fs[abi_decode_frame_def] >> sym_tac >> first_x_assum irule >> decide_tac) >>
  fs[] >> rpt strip_tac >> simp[] >> decide_tac
QED

Theorem abi_encode_bytes_contract_path:
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
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+10 /\
    (!q. not_fresh_at st q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint un (Var q) = op_taint tn (Var q)) /\
    mem_agree_outside
      {i | w2n b <= i /\ i < w2n b+(32+contractABI$ceil32 (LENGTH bs))}
      s.vs_memory t.vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b+(32+contractABI$ceil32 (LENGTH bs))) ==>
      (i IN un.t_mem <=> i IN tn.t_mem))
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
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs)` by simp[abi_encoder_ceil32_bounds] >>
  drule_all abi_encode_bytes_frame_projection >> strip_tac >>
  `LENGTH (enc at (contractABI$BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_bytes_encoding] >>
  qexistsl_tac [`p`, `t`, `H`, `un`] >> asm_rewrite_tac []
QED
