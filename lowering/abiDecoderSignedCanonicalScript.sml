(* Canonical ABI signed integers satisfy the actual SIGNEXTEND clamp. *)
Theory abiDecoderSignedCanonical
Ancestors
  abiDecoderSignedWord abiDecoderNumericWord abiDecoderClamp abiDecoderContract
  vyperABI vyperValue exprLowering valueEncoding venomState contractABI
  integer_word words arithmetic list rich_list
Libs
  intLib

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_SIGNED_CANONICAL_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI canonical signed clamp not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderSignedCanonical");
