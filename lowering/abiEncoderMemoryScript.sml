(* Padded-memory observations and the bytes encoder's zero-then-copy update. *)
Theory abiEncoderMemory
Ancestors
  abiDecoderTypedContract abiStaticAggregateProps abiDecoderFrame abiDecoderContract
  valueEncoding valueEncodingProps valueEncodingProofs venomMemProps venomState venomExecSemantics
  contractABI byte words list rich_list arithmetic

Theorem abi_encoder_mem_split:
  !off m n mem. mem_bytes_at off (m+n) mem =
    mem_bytes_at off m mem ++ mem_bytes_at (off+m) n mem
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`off`, `m`, `n`, `mem ++ REPLICATE (off + m + n) 0w`]
    mem_bytes_at_split) >> simp[mem_bytes_at_append_zero]
QED

Theorem abi_encoder_word_window:
  mem_bytes_at off 32 mem = word_to_bytes (mem_word_at off mem) T
Proof
  simp_tac bool_ss [mem_word_at_bytes] >> irule EQ_SYM >>
  irule word_bytes_roundtrip_256 >> simp[]
QED

Theorem abi_encoder_zero_aux[local]:
  !n. word_to_bytes_aux n (0w:bytes32) T = REPLICATE n 0w
Proof
  Induct >> simp[word_to_bytes_aux_def, get_byte_def, ZERO_SHIFT, w2w_0,
                 GSYM SNOC_APPEND, SNOC_REPLICATE]
QED

Theorem abi_encoder_zero_word:
  word_to_bytes (0w:bytes32) T = REPLICATE 32 0w /\
  mem_bytes_at p 32 (mstore p 0w s).vs_memory = REPLICATE 32 0w
Proof
  simp[word_to_bytes_def, abi_encoder_zero_aux] >>
  simp[abi_encoder_word_window, mstore_mem_word_at_same, word_to_bytes_def, abi_encoder_zero_aux]
QED

Theorem abi_encoder_zero_subwindow:
  off + n <= 32 ==>
  mem_bytes_at (p+off) n (mstore p 0w s).vs_memory = REPLICATE n 0w
Proof
  strip_tac >> `off + (n + (32 - off - n)) = 32` by decide_tac >>
  mp_tac (Q.SPECL [`p`, `REPLICATE off 0w`, `REPLICATE n 0w`,
    `REPLICATE (32 - off - n) 0w`, `(mstore p 0w s).vs_memory`]
    abi_decoder_source_subwindow) >>
  impl_tac >- asm_simp_tac (srw_ss()) [REPLICATE_APPEND, GSYM ADD_ASSOC,
    abi_encoder_zero_word] >> simp[]
QED

Theorem abi_encoder_bytes_source_prefix:
  mem_word_at sb mem = n2w (LENGTH bs) /\
  mem_bytes_at (sb+32) (LENGTH bs) mem = bs ==>
  mem_bytes_at sb (32+LENGTH bs) mem =
    word_to_bytes (n2w (LENGTH bs):bytes32) T ++ bs
Proof
  strip_tac >> simp[Once abi_encoder_mem_split, abi_encoder_word_window]
QED

Theorem abi_encoder_bytes_zero_copy:
  LENGTH bs <= rounded /\ rounded <= LENGTH bs + 32 /\
  (sb + (32 + LENGTH bs) <= db \/ db + (32+rounded) <= sb) /\
  mem_word_at sb s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (sb+32) (LENGTH bs) s.vs_memory = bs ==>
  mem_bytes_at db (32+rounded)
    (mcopy db sb (32+LENGTH bs) (mstore (db+rounded) 0w s)).vs_memory =
    word_to_bytes (n2w (LENGTH bs):bytes32) T ++ bs ++ REPLICATE (rounded-LENGTH bs) 0w
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `mem_bytes_at sb (32+LENGTH bs) (mstore (db+rounded) 0w s).vs_memory =
   mem_bytes_at sb (32+LENGTH bs) s.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `mem_bytes_at sb (32+LENGTH bs) s.vs_memory =
   word_to_bytes (n2w (LENGTH bs):bytes32) T ++ bs` by
    (irule abi_encoder_bytes_source_prefix >> asm_simp_tac bool_ss []) >>
  `32 + LENGTH bs - rounded + (rounded - LENGTH bs) <= 32 /\
   db+rounded+(32+LENGTH bs-rounded) = db+32+LENGTH bs /\
   32+LENGTH bs+(rounded-LENGTH bs) = 32+rounded` by decide_tac >>
  mp_tac (Q.INST [`p` |-> `db+rounded`, `off` |-> `32+LENGTH (bs:byte list)-rounded`,
    `n` |-> `rounded-LENGTH (bs:byte list)`] abi_encoder_zero_subwindow) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`db`, `32+LENGTH (bs:byte list)`, `rounded-LENGTH (bs:byte list)`,
    `(mcopy db sb (32+LENGTH (bs:byte list)) (mstore (db+rounded) 0w s)).vs_memory`]
    abi_encoder_mem_split) >>
  asm_simp_tac (srw_ss()) [mcopy_mem_bytes_at_same, mcopy_mem_bytes_at_disjoint, APPEND_ASSOC] >>
  disch_then kall_tac >> PURE_REWRITE_TAC [ADD_ASSOC] >> first_assum ACCEPT_TAC
QED

Theorem abi_encoder_bytes_write_frame:
  cnt <= rounded ==>
  abi_decode_frame db (32+rounded) s
    (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s))
Proof
  strip_tac >> simp_tac bool_ss [abi_decode_frame_def] >> conj_tac
  >- (rpt strip_tac >> (irule EQ_TRANS >>
      qexists_tac `mem_bytes_at p k (mstore (db+rounded) 0w s).vs_memory` >> conj_tac
      >- (irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
      irule mstore_mem_bytes_at_disjoint >> decide_tac)) >>
  simp_tac bool_ss [mcopy_def, mstore_def, write_memory_with_expansion_def,
    LET_THM, venom_state_accfupds]
QED

Theorem abi_encoder_bytes_write_memory_cong:
  s.vs_memory = t.vs_memory ==>
  (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s)).vs_memory =
  (mcopy db sb (32+cnt) (mstore (db+rounded) 0w t)).vs_memory
Proof
  simp_tac bool_ss [mcopy_def, mstore_def, write_memory_with_expansion_def,
    LET_THM, venom_state_accfupds]
QED

Theorem abi_encoder_frame_memory:
  abi_decode_frame db sz s t /\ u.vs_memory = t.vs_memory /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_data_section = s.vs_data_section ==>
  abi_decode_frame db sz s u
Proof
  simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >> asm_simp_tac bool_ss []
QED
