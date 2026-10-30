(* TOP-LEVEL: connect the bytestring encoder's word arithmetic and exact
   memory writes to the ABI length and padded payload layout. *)
Theory abiBytestringMemory
Ancestors
  abiBytestringExec abiBytestringPadding memoryReadProps valueEncoding valueEncodingProps
  venomState venomExecSemantics venomMemProps contractABI
  list rich_list words arithmetic bit
Libs fcpLib wordsLib

Theorem word_and_ceil32_mask:
  !(w:bytes32).
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w && w =
      (w >>> 5) << 5
Proof
  gen_tac >>
  `(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:bytes32) =
      ~31w` by EVAL_TAC >> pop_assum SUBST1_TAC >>
  `!bit_index. BIT bit_index 31 <=> bit_index < 5` by
    (qx_gen_tac `bit_index` >>
     mp_tac (Q.SPECL [`bit_index`, `5`] BIT_EXP_SUB1) >> simp[]) >>
  rw_tac (bool_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [word_and_def, word_1comp_def, word_lsr_def, word_lsl_def, n2w_def,
     dimindex_256] >>
  rename1 `bit_index < 256` >> Cases_on `5 <= bit_index` >> fs[]
QED

Theorem bytestring_round_word_n2w:
  !n. n + 31 < dimword(:256) ==>
    bytestring_round_word (n2w n) = n2w (ceil32 n)
Proof
  rpt gen_tac >> strip_tac >> fs[] >>
  simp[bytestring_round_word_def, word_and_ceil32_mask, word_add_n2w,
    GSYM n2w_DIV, word_lsl_n2w, ceil32_def, ADD_COMM, MULT_COMM]
QED

Theorem ceil32_bounds:
  !n. n <= ceil32 n /\ ceil32 n < n + 32
Proof
  gen_tac >> conj_tac >- simp[] >> rewrite_tac[ceil32_def] >>
  mp_tac (Q.SPEC `n + 31` (MATCH_MP DIVISION (DECIDE ``0 < 32n``))) >>
  simp[MULT_COMM] >> decide_tac
QED

Theorem bytestring_copy_state_natural:
  !dst_addr src_addr ss n.
    mload (w2n src_addr) ss = n2w n /\
    32 + ceil32 n < dimword(:256) /\
    w2n dst_addr + ceil32 n < dimword(:256) ==>
    bytestring_copy_state dst_addr src_addr ss =
      mcopy (w2n dst_addr) (w2n src_addr) (32 + n)
        (mstore (w2n dst_addr + ceil32 n) 0w ss)
Proof
  rpt gen_tac >> strip_tac >>
  `n <= ceil32 n` by simp[] >>
  `n + 31 < dimword(:256) /\ n + 32 < dimword(:256) /\
   ceil32 n < dimword(:256)` by decide_tac >>
  `bytestring_round_word (n2w n) = n2w (ceil32 n)` by
    (irule bytestring_round_word_n2w >> simp[]) >>
  fs[] >>
  simp[bytestring_copy_state_def, LET_THM, word_add_def, w2n_n2w, ADD_COMM]
QED

Theorem bytestring_encoded_size:
  !bs. LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) = 32 + ceil32 (LENGTH bs)
Proof
  gen_tac >> simp[enc_def, LET_THM] >>
  mp_tac (Q.SPEC `LENGTH (bs:word8 list)` ceil32_bounds) >> decide_tac
QED

Theorem bytestring_copy_state_encoded:
  !dst_addr src_addr ss bs.
    mload (w2n src_addr) ss = n2w (LENGTH bs) /\
    read_memory (w2n src_addr + 32) (LENGTH bs) ss = bs /\
    32 + ceil32 (LENGTH bs) < dimword(:256) /\
    w2n dst_addr + ceil32 (LENGTH bs) < dimword(:256) /\
    (w2n src_addr + 32 + LENGTH bs <= w2n dst_addr + ceil32 (LENGTH bs) \/
     w2n dst_addr + ceil32 (LENGTH bs) + 32 <= w2n src_addr) ==>
    read_memory (w2n dst_addr) (32 + ceil32 (LENGTH bs))
      (bytestring_copy_state dst_addr src_addr ss) =
    enc (Bytes NONE) (contractABI$BytesV bs)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  mp_tac (Q.SPECL [`dst_addr`, `src_addr`, `ss`, `LENGTH (bs:word8 list)`]
    bytestring_copy_state_natural) >> impl_tac >- simp[] >>
  disch_then SUBST1_TAC >>
  simp_tac (srw_ss()) [enc_def, LET_THM] >>
  irule bytestring_padding_copy >> simp[] >>
  mp_tac (Q.SPEC `LENGTH (bs:word8 list)` ceil32_bounds) >> decide_tac
QED

Theorem bytestring_encoded_size_word:
  !src_addr ss bs.
    mload (w2n src_addr) ss = n2w (LENGTH bs) /\
    32 + ceil32 (LENGTH bs) < dimword(:256) ==>
    32w + bytestring_round_word (mload (w2n src_addr) ss) =
      n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH bs + 31 < dimword(:256)` by
    (mp_tac (Q.SPEC `LENGTH (bs:word8 list)` ceil32_bounds) >> decide_tac) >>
  simp[bytestring_encoded_size, bytestring_round_word_n2w, word_add_n2w]
QED

Theorem bytestring_copy_state_frame:
  !offset read_len dst_addr src_addr ss n.
    mload (w2n src_addr) ss = n2w n /\
    32 + ceil32 n < dimword(:256) /\
    w2n dst_addr + ceil32 n < dimword(:256) /\
    (offset + read_len <= w2n dst_addr \/
     w2n dst_addr + ceil32 n + 32 <= offset) ==>
    read_memory offset read_len (bytestring_copy_state dst_addr src_addr ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  mp_tac (Q.SPECL [`dst_addr`, `src_addr`, `ss`, `n`]
    bytestring_copy_state_natural) >> impl_tac >- simp[] >>
  disch_then SUBST1_TAC >> irule bytestring_padding_frame >> simp[]
QED

Theorem bytestring_copy_state_memory_length:
  !dst_addr src_addr ss.
    LENGTH ss.vs_memory <=
      LENGTH (bytestring_copy_state dst_addr src_addr ss).vs_memory
Proof
  rpt gen_tac >>
  simp[bytestring_copy_state_def, mcopy_def, LET_THM,
    LENGTH_write_memory_with_expansion, LENGTH_mstore_eq, MAX_DEF]
QED
