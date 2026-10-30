Theory abiDecoderSigned
Ancestors
  venomMemProps abiDecoderClamp venomExecSemantics venomState integer_word words arithmetic
  abiDecoderNumericWord abiDecoderContract vyperABI vyperValue exprLowering valueEncoding
  contractABI list rich_list
Libs
  wordsLib intLib

(* ===== Word ===== *)

(* Signed canonical-word arithmetic used by primitive decoder validation. *)

Theorem abi_signed_bit_one[local]:
  bit$BIT i 1 <=> i = 0
Proof
  mp_tac (Q.SPECL [`i`, `0`] bitTheory.BIT_TWO_POW) >>
  simp_tac bool_ss [EXP] >> metis_tac[]
QED

Theorem abi_decoder_sign_extend_cast_bit:
  dimindex (:'a) = 8 * (n + 1) /\ n < 31 ==>
  ((sw2sw (w:'a word) : bytes32) >>> (8 * n + 7)) && 1w =
    if word_msb w then 1w else 0w
Proof
  strip_tac >>
  `8 * n + 7 = dimindex (:'a) - 1 /\ dimindex (:'a) <= 256` by decide_tac >>
  Cases_on `word_msb w` >>
  rw_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [word_and_def, word_lsr_def, sw2sw, word_msb_def, word_index, word_0,
     dimindex_256, abi_signed_bit_one] >>
  Cases_on `i = 0` >> gvs[sw2sw, word_msb_def] >>
  `8 * (n + 1) - 1 = dimindex (:'a) - 1` by decide_tac >> asm_rewrite_tac[]
QED

Theorem abi_decoder_sign_extend_cast_mask:
  dimindex (:'a) <= 256 ==>
  (if word_msb (w:'a word) then
     (sw2sw w : bytes32) || ~(1w << dimindex (:'a) - 1w)
   else (sw2sw w : bytes32) && (1w << dimindex (:'a) - 1w)) = sw2sw w
Proof
  strip_tac >> Cases_on `word_msb w` >>
  simp_tac bool_ss [] >>
  rw_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [word_and_def, word_or_def, word_1comp_def, sw2sw, SHIFT_1_SUB_1,
     dimindex_256] >>
  Cases_on `i < dimindex (:'a)` >> gvs[]
QED

Theorem abi_decoder_sign_extend_cast:
  dimindex (:'a) = 8 * (n + 1) /\ n < 32 ==>
  sign_extend (n2w n) (sw2sw (w:'a word) : bytes32) = sw2sw w
Proof
  strip_tac >> `n < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  Cases_on `30 < n`
  >- simp[venomExecSemanticsTheory.sign_extend_def, w2n_n2w] >>
  `n < 31 /\ dimindex (:'a) <= 256 /\ 8 * n + 8 = dimindex (:'a)` by decide_tac >>
  drule_all abi_decoder_sign_extend_cast_bit >> strip_tac >>
  Cases_on `word_msb w` >>
  mp_tac (Q.ISPEC `w:'a word` (GEN_ALL abi_decoder_sign_extend_cast_mask)) >>
  asm_simp_tac (std_ss ++ numSimps.ARITH_ss)
    [venomExecSemanticsTheory.sign_extend_def, w2n_n2w, LET_THM, GREATER_DEF] >> simp[]
QED

Theorem abi_decoder_sign_extend_i2w:
  dimindex (:'a) = 8 * (n + 1) /\ n < 32 /\
  INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a) ==>
  sign_extend (n2w n) (i2w i : bytes32) = i2w i
Proof
  strip_tac >> `dimindex (:'a) <= 256` by decide_tac >>
  `(sw2sw (i2w i : 'a word) : bytes32) = i2w i` by
    (irule sw2sw_i2w >> simp[]) >>
  drule_all abi_decoder_sign_extend_cast >>
  disch_then (qspec_then `i2w i : 'a word` mp_tac) >> simp[]
QED

Theorem abi_decoder_sign_extend_8:
  sign_extend 0w (sw2sw (w:word8) : bytes32) = sw2sw w
Proof
  mp_tac (Q.INST [`n` |-> `0`]
    (INST_TYPE [alpha |-> ``:8``] abi_decoder_sign_extend_cast)) >> simp[]
QED

(* ===== Canonical ===== *)

(* Canonical ABI signed integers satisfy the actual SIGNEXTEND clamp. *)

Theorem abi_decoder_signed_bound:
  within_int_bound (Signed (dimindex (:'a))) i <=>
  INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a)
Proof
  simp[within_int_bound_def, integer_wordTheory.INT_MIN_def,
       integer_wordTheory.INT_MAX_def, wordsTheory.INT_MIN_def, LET_THM] >>
  Cases_on `i < 0` >> simp[] >> intLib.COOPER_TAC
QED

(* ABI integers have one of 32 byte-aligned widths. Each branch instantiates
   the same polymorphic sign-extension theorem at its corresponding word type. *)
Theorem abi_decoder_integer_widths:
  valid_int_bound bits ==>
  MEM bits [8;16;24;32;40;48;56;64;72;80;88;96;104;112;120;128;
             136;144;152;160;168;176;184;192;200;208;216;224;232;240;248;256]
Proof
  pure_rewrite_tac [valid_int_bound_def] >> strip_tac >>
  `bits = 8 * (bits DIV 8)` by
    (mp_tac (Q.SPEC `bits` (SIMP_RULE arith_ss [] (Q.SPEC `8` DIVISION))) >>
     asm_simp_tac arith_ss [MULT_COMM]) >>
  `0 < bits DIV 8 /\ bits DIV 8 <= 32` by decide_tac >>
  pure_rewrite_tac [GSYM (EVAL ``MAP (\i. 8 * (i + 1)) (COUNT_LIST 32)``)] >>
  simp_tac bool_ss [MEM_MAP, MEM_COUNT_LIST] >>
  qexists_tac `bits DIV 8 - 1` >> decide_tac
QED

Theorem abi_decoder_signed_canonical_i2w:
  valid_int_bound bits /\ within_int_bound (Signed bits) i ==>
  sign_extend (n2w (bits DIV 8 - 1)) (i2w i : bytes32) = i2w i
Proof
  strip_tac >>
  drule abi_decoder_integer_widths >> strip_tac >>
  qpat_x_assum `MEM bits _` (strip_assume_tac o PURE_REWRITE_RULE [MEM]) >> gvs[] >>
  FIRST (List.tabulate (32, fn j =>
    irule (SIMP_RULE (srw_ss()) [GSYM abi_decoder_signed_bound]
      (INST [``n:num`` |-> numSyntax.term_of_int j]
        (INST_TYPE [alpha |-> fcpLib.index_type (Arbnum.fromInt (8 * (j + 1)))]
          abi_decoder_sign_extend_i2w))))) >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem abi_decoder_canonical_int_clamp:
  valid_int_bound bits /\ within_int_bound (Signed bits) i /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (Int bits) (contractABI$IntV i) ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT (IntT bits)))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  strip_tac >>
  `abi_decode_load opc (n2w sb : bytes32) s = i2w i` by
    (irule abi_decoder_canonical_word_load >> gvs[enc_def, enc_number_def]) >>
  Cases_on `bits = 256` >> gvs[type_to_abi_clamp_def, abi_decoder_clamp_valid_def] >>
  drule_all abi_decoder_signed_canonical_i2w >> simp[]
QED

Theorem abi_decoder_canonical_decimal_clamp:
  within_int_bound (Signed 168) i /\ sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (Int 168) (contractABI$IntV i) ==>
  abi_decoder_clamp_valid (IntClamp 168 T)
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  strip_tac >>
  `abi_decode_load opc (n2w sb : bytes32) s = i2w i` by
    (irule abi_decoder_canonical_word_load >> gvs[enc_def, enc_number_def]) >>
  `valid_int_bound 168` by simp[valid_int_bound_def] >>
  drule_all abi_decoder_signed_canonical_i2w >> simp[abi_decoder_clamp_valid_def]
QED
