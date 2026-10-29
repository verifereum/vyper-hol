(* Canonical byte windows lifted to the actual decoder source loads. *)
Theory abiCanonicalLoad
Ancestors
  venomMemProps
  abiCanonicalWindows abiDecoderContract valueEncodingProps valueEncodingProofs valueEncoding
  abiDecodeRanges contractABI byte words arithmetic list rich_list venomState

Theorem mem_bytes_at_window:
  !sb off n len mem.
  off + n <= len ==>
  TAKE n (DROP off (mem_bytes_at sb len mem)) =
    mem_bytes_at (sb + off) n mem
Proof
  rpt strip_tac >>
  `n <= len - off` by decide_tac >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ, LENGTH_DROP, MIN_ALT] >>
  rpt strip_tac >> rename1 `i < n` >>
  `off + i < len` by decide_tac >>
  simp[EL_TAKE, EL_DROP, EL_mem_bytes_at] >>
  pure_rewrite_tac[ADD_ASSOC] >> REFL_TAC
QED

Theorem abi_decode_load_bytes:
  p < dimword (:'a) ==>
  abi_decode_load opc (n2w p : 'a word) s =
    word_of_bytes T (0w:256 word) (mem_bytes_at p 32 (abi_decode_source opc s))
Proof
  strip_tac >> Cases_on `opc = MLOAD` >>
  simp[abi_decode_load_def, abi_decode_source_def, mload_def,
       mem_bytes_at_def, w2n_n2w]
QED

Theorem canonical_member_offset_word:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty ==>
  word_of_bytes T (0w:256 word)
    (TAKE 32 (DROP (SUM (MAP abi_member_head_size pre))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))))) =
    n2w (head_lengths (pre ++ ty::post) 0 +
         SUM (MAP2 abi_member_tail_size pre pvs))
Proof
  strip_tac >> drule_all canonical_member_head_window >>
  asm_simp_tac bool_ss [LET_THM, abi_member_head_size_def, enc_number_def] >>
  strip_tac >> asm_rewrite_tac[] >> irule word_of_bytes_word_to_bytes >>
  simp[dividesTheory.divides_def]
QED

Theorem abi_decode_load_window:
  off + 32 <= len /\ sb + off < dimword (:'a) ==>
  abi_decode_load opc (n2w (sb + off) : 'a word) s =
    word_of_bytes T (0w:256 word)
      (TAKE 32 (DROP off (mem_bytes_at sb len (abi_decode_source opc s))))
Proof
  strip_tac >> asm_simp_tac bool_ss [abi_decode_load_bytes] >>
  AP_TERM_TAC >> irule EQ_SYM >> irule mem_bytes_at_window >>
  first_assum ACCEPT_TAC
QED

Theorem canonical_member_offset_load:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post))
    (ListV (pvs ++ v::rest)))) (abi_decode_source opc s) =
      enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) /\
  sb + LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))) <
    dimword (:256) ==>
  abi_decode_load opc
    (n2w (sb + SUM (MAP abi_member_head_size pre)) : 256 word) s =
  n2w (head_lengths (pre ++ ty::post) 0 +
       SUM (MAP2 abi_member_tail_size pre pvs))
Proof
  strip_tac >> drule_all canonical_member_ranges >>
  asm_simp_tac bool_ss [LET_THM, abi_member_head_size_def] >> strip_tac >>
  `sb + SUM (MAP abi_member_head_size pre) < dimword (:256)` by decide_tac >>
  irule EQ_TRANS >>
  qexists_tac `word_of_bytes T (0w:256 word)
    (TAKE 32 (DROP (SUM (MAP abi_member_head_size pre))
      (mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post))
        (ListV (pvs ++ v::rest)))) (abi_decode_source opc s))))` >>
  conj_tac
  >- (irule abi_decode_load_window >> simp[]) >>
  asm_rewrite_tac[] >> irule canonical_member_offset_word >> simp[]
QED
