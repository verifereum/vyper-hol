(* Fixed-byte ABI words have zero low padding and pass the SHL clamp. *)
Theory abiDecoderFixedBytes
Ancestors
  abiDecoderClamp abiDecoderContract abiCanonicalLoad valueEncodingProofs
  exprLowering valueEncoding venomState contractABI byte words list rich_list arithmetic

Theorem abi_fixed_bytes_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_decoder_set_byte_low_bit:
  a < 32 /\ j < 8 * (31 - a) /\ ~(w:bytes32) ' j ==>
  ~(set_byte (n2w a) b w T) ' j
Proof
  strip_tac >> `a < dimword (:256) /\ j < 256` by
    (simp[dimword_def] >> decide_tac) >>
  rw_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [set_byte_def, byte_index_def, w2n_n2w, LESS_MOD, LET_THM,
     word_slice_alt_def, word_or_def, word_lsl_def, w2w, abi_fixed_bytes_dimindex]
QED

Theorem abi_decoder_bytes_cons_low_bit[local]:
  (!a j. a + LENGTH bs <= 32 /\ j < 8 * (32 - (a + LENGTH bs)) ==>
    ~(word_of_bytes T (n2w a) bs : bytes32) ' j) /\
  a + LENGTH (h::bs) <= 32 /\ j < 8 * (32 - (a + LENGTH (h::bs))) ==>
  ~(word_of_bytes T (n2w a) (h::bs) : bytes32) ' j
Proof
  strip_tac >>
  `a < 32 /\ j < 8 * (31 - a) /\ a + 1 + LENGTH bs <= 32 /\
   j < 8 * (32 - (a + 1 + LENGTH bs))` by (fs[] >> decide_tac) >>
  simp_tac bool_ss [word_of_bytes_def, word_add_n2w] >>
  irule abi_decoder_set_byte_low_bit >> asm_simp_tac bool_ss [] >>
  first_x_assum irule >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_bytes_low_bit:
  !bs a j. a + LENGTH bs <= 32 /\ j < 8 * (32 - (a + LENGTH bs)) ==>
  ~(word_of_bytes T (n2w a) bs : bytes32) ' j
Proof
  Induct >- simp[word_of_bytes_def, word_0] >>
  rpt gen_tac >> strip_tac >> irule abi_decoder_bytes_cons_low_bit >> simp[]
QED

Theorem abi_decoder_fixed_bytes_shift_zero:
  LENGTH bs <= 32 ==>
  (word_of_bytes T 0w bs : bytes32) << w2n (n2w (LENGTH bs * 8) : bytes32) = 0w
Proof
  strip_tac >> `8 * LENGTH bs < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  simp[w2n_n2w] >>
  rw_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [word_lsl_def, word_0, abi_fixed_bytes_dimindex] >>
  rename1 `bit_idx < 256` >>
  Cases_on `8 * LENGTH bs <= bit_idx` >> asm_simp_tac bool_ss [] >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.SPECL [`bs`, `0`] abi_decoder_bytes_low_bit)) >> simp[] >> decide_tac
QED

Theorem abi_decoder_canonical_fixed_bytes_clamp:
  has_type (Bytes (SOME m)) av /\ sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (Bytes (SOME m)) av ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT (BytesT (Fixed m))))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  Cases_on `av` >>
  simp_tac bool_ss [has_type_def, valid_bytes_bound_def, valid_length_def, LET_THM] >>
  rpt strip_tac >>
  rename1 `mem_bytes_at sb 32 (abi_decode_source opc s) =
    enc (Bytes (SOME m)) (contractABI$BytesV bs)` >>
  fs[] >>
  `LENGTH bs <= 32` by decide_tac >>
  `abi_decode_load opc (n2w sb : bytes32) s = word_of_bytes T 0w bs` by
    (asm_simp_tac bool_ss [abi_decode_load_bytes] >>
     asm_simp_tac (srw_ss()) [enc_def, TAKE_LENGTH_TOO_LONG, word_of_bytes_append_zero]) >>
  drule abi_decoder_fixed_bytes_shift_zero >>
  Cases_on `m = 32` >> simp[type_to_abi_clamp_def, abi_decoder_clamp_valid_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_FIXED_BYTES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI canonical fixed bytes not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderFixedBytes");
