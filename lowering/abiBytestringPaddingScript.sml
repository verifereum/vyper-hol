(* TOP-LEVEL: pre-zeroing the last payload word followed by a live-byte copy
   establishes the ABI header, payload and zero padding. The source must be
   disjoint from the preliminary zero store; source padding is unrestricted. *)
Theory abiBytestringPadding
Ancestors
  memoryReadProps valueEncoding valueEncodingProps valueEncodingProofs
  venomState venomExecSemantics venomMemProps byte
  list rich_list arithmetic words
Libs wordsLib

Theorem read_memory_subwindow = memoryReadPropsTheory.read_memory_subwindow;

Theorem word_to_bytes_zero_256:
  word_to_bytes (0w:bytes32) T = REPLICATE 32 (0w:word8)
Proof
  EVAL_TAC
QED

Theorem read_memory_zero_store:
  !offset skip read_len ss.
    skip + read_len <= 32 ==>
    read_memory (offset + skip) read_len (mstore offset 0w ss) = REPLICATE read_len 0w
Proof
  rpt gen_tac >> strip_tac >>
  `read_len <= 32 - skip` by decide_tac >>
  `MIN read_len (32 - skip) = read_len` by simp[MIN_DEF] >>
  mp_tac (Q.SPECL [`offset`, `32`, `skip`, `read_len`, `mstore offset 0w ss`]
    read_memory_subwindow) >>
  impl_tac >- simp[] >>
  PURE_REWRITE_TAC[read_memory_word, mload_mstore_same, word_to_bytes_zero_256] >>
  PURE_REWRITE_TAC[DROP_REPLICATE] >>
  PURE_REWRITE_TAC[REPLICATE_GENLIST] >>
  asm_simp_tac bool_ss [TAKE_GENLIST]
QED

Theorem bytestring_padding_zero:
  !dst src n rounded ss.
    n <= rounded /\ rounded <= n + 32 ==>
    read_memory (dst + 32 + n) (rounded - n)
      (mcopy dst src (32 + n) (mstore (dst + rounded) 0w ss)) =
      REPLICATE (rounded - n) 0w
Proof
  rpt gen_tac >> strip_tac >>
  `read_memory (dst + 32 + n) (rounded - n)
      (mcopy dst src (32 + n) (mstore (dst + rounded) 0w ss)) =
    read_memory (dst + 32 + n) (rounded - n) (mstore (dst + rounded) 0w ss)` by
    (irule read_memory_mcopy_disjoint >> decide_tac) >>
  `(dst + rounded) + (32 + n - rounded) = dst + 32 + n /\
   (32 + n - rounded) + (rounded - n) = 32` by decide_tac >>
  mp_tac (Q.SPECL [`dst + rounded`, `32 + n - rounded`, `rounded - n`, `ss`]
    read_memory_zero_store) >> simp[]
QED

Theorem bytestring_padding_copy:
  !dst src rounded bs ss.
    mload src ss = n2w (LENGTH bs) /\ read_memory (src + 32) (LENGTH bs) ss = bs /\
    LENGTH bs <= rounded /\ rounded <= LENGTH bs + 32 /\
    (src + 32 + LENGTH bs <= dst + rounded \/ dst + rounded + 32 <= src) ==>
    read_memory dst (32 + rounded)
      (mcopy dst src (32 + LENGTH bs) (mstore (dst + rounded) 0w ss)) =
      word_to_bytes (n2w (LENGTH bs):bytes32) T ++ bs ++
        REPLICATE (rounded - LENGTH bs) 0w
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `read_memory src (32 + LENGTH bs) (mstore (dst + rounded) 0w ss) =
    read_memory src (32 + LENGTH bs) ss` by
    (irule read_memory_mstore_disjoint >> decide_tac) >>
  `read_memory src (32 + LENGTH bs) ss =
     word_to_bytes (n2w (LENGTH bs):bytes32) T ++ bs` by
    (mp_tac (Q.SPECL [`src`, `32`, `LENGTH (bs:word8 list)`, `ss`] read_memory_split) >>
     simp[read_memory_word]) >>
  `read_memory (dst + 32 + LENGTH bs) (rounded - LENGTH bs)
      (mcopy dst src (32 + LENGTH bs) (mstore (dst + rounded) 0w ss)) =
    REPLICATE (rounded - LENGTH bs) 0w` by
    (irule bytestring_padding_zero >> simp[]) >>
  `(32 + LENGTH bs) + (rounded - LENGTH bs) = 32 + rounded` by decide_tac >>
  mp_tac (Q.SPECL [`dst`, `32 + LENGTH (bs:word8 list)`, `rounded - LENGTH (bs:word8 list)`,
    `mcopy dst src (32 + LENGTH (bs:word8 list)) (mstore (dst + rounded) 0w ss)`]
      read_memory_split) >>
  qpat_x_assum `(32 + LENGTH bs) + (rounded - LENGTH bs) = _`
    (fn th => PURE_REWRITE_TAC[th]) >>
  PURE_REWRITE_TAC[read_memory_mcopy_self] >>
  qpat_x_assum `read_memory src (32 + LENGTH bs) (mstore _ _ _) = _`
    (fn th => PURE_REWRITE_TAC[th]) >>
  qpat_x_assum `read_memory src (32 + LENGTH bs) ss = _`
    (fn th => PURE_REWRITE_TAC[th]) >>
  `dst + (32 + LENGTH bs) = dst + 32 + LENGTH bs` by decide_tac >>
  pop_assum (fn th => PURE_REWRITE_TAC[th]) >>
  qpat_x_assum `read_memory (dst + 32 + LENGTH bs) _ _ = _`
    (fn th => PURE_REWRITE_TAC[th]) >>
  PURE_REWRITE_TAC[APPEND_ASSOC] >> simp[]
QED

Theorem bytestring_padding_frame:
  !offset read_len dst src n rounded ss.
    n <= rounded /\
    (offset + read_len <= dst \/ dst + rounded + 32 <= offset) ==>
    read_memory offset read_len
      (mcopy dst src (32 + n) (mstore (dst + rounded) 0w ss)) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `read_memory offset read_len
      (mcopy dst src (32 + n) (mstore (dst + rounded) 0w ss)) =
    read_memory offset read_len (mstore (dst + rounded) 0w ss)` by
    (irule read_memory_mcopy_disjoint >> decide_tac) >>
  pop_assum SUBST1_TAC >> irule read_memory_mstore_disjoint >> decide_tac
QED
