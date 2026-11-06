(* Pure guard and result encoding for a full extract32 slice. *)
Theory bodyMemTbExtract32Encoding
Ancestors
  convertScalarEncoding valueEncoding byte words list rich_list cv_std arithmetic
  vyperValue vyperAST moduleLoweringProps

Theorem extract32_fixed_test:
  LENGTH bs = 32 /\ m <= 32 ==>
  ((word_of_bytes_be bs:bytes32) << (8 * m) = 0w <=>
   EVERY (\b. b = 0w) (DROP m bs))
Proof
  strip_tac >>
  `m <= LENGTH bs /\ LENGTH bs <= 32` by simp[] >>
  drule_all scalar_fixed_narrow_test >> simp[PAD_RIGHT]
QED

Theorem extract32_fixed_encoding:
  LENGTH bs = 32 /\ EVERY (\b. b = 0w) (DROP m bs) ==>
  typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV (TAKE m bs)) =
    (word_of_bytes_be bs:bytes32)
Proof
  strip_tac >> drule scalar_fixed_narrow >>
  simp[scalar_fixed_encoding, PAD_RIGHT]
QED

Theorem extract32_address_parts[local]:
  LENGTH bs = 32 ==>
  w2n (word_of_bytes_be bs:bytes32) =
    num_of_bytes (REVERSE (DROP 12 bs)) +
    2 ** 160 * num_of_bytes (REVERSE (TAKE 12 bs))
Proof
  strip_tac >>
  `12 <= LENGTH bs /\ LENGTH bs <= 32` by simp[] >>
  qspec_then `bs` (qspec_then `12` mp_tac) scalar_reverse_split_num >>
  simp[] >> strip_tac >>
  qspec_then `bs` mp_tac scalar_fixed_encoding_bound >> simp[] >> strip_tac >>
  qspec_then `bs` mp_tac scalar_fixed_encoding_num >>
  simp[PAD_RIGHT, w2n_n2w, dimword_def]
QED

Theorem extract32_address_test:
  LENGTH bs = 32 ==>
  (w2n (word_of_bytes_be bs:bytes32) < 2 ** 160 <=>
   EVERY (\b. b = 0w) (TAKE 12 bs))
Proof
  strip_tac >> drule extract32_address_parts >> strip_tac >>
  qspec_then `REVERSE (DROP 12 bs)` mp_tac num_of_bytes_lt >>
  simp[] >> strip_tac >>
  `EVERY (\b. b = 0w) (TAKE 12 bs) <=>
   num_of_bytes (REVERSE (TAKE 12 bs)) = 0` by
    simp[scalar_num_of_bytes_zero, EVERY_REVERSE] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem extract32_address_encoding:
  LENGTH bs = 32 /\ EVERY (\b. b = 0w) (TAKE 12 bs) ==>
  typed_val_to_w256 (BaseTV AddressT) (BytesV (DROP 12 bs)) =
    (word_of_bytes_be bs:bytes32)
Proof
  strip_tac >> drule extract32_address_parts >> strip_tac >>
  `num_of_bytes (REVERSE (TAKE 12 bs)) = 0` by
    simp[scalar_num_of_bytes_zero, EVERY_REVERSE] >>
  `LENGTH (DROP 12 bs) <= 32` by simp[] >>
  simp[scalar_address_encoding, scalar_address_encoding_num] >>
  gvs[] >> metis_tac[wordsTheory.n2w_w2n]
QED
