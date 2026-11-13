(* Pure guard and result encoding for a full extract32 slice. *)
Theory bodyMemTbExtract32Encoding
Ancestors
  convertScalarEncoding valueEncoding byte words list rich_list cv_std arithmetic
  vyperValue vyperAST moduleLoweringProps vyperContext vyperValueOperation
  vyperTypeSystem integer_word

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

Theorem extract32_slice_guards:
  !bs m. LENGTH bs = 32 ==>
    evaluate_extract32 bs 0 (UintT m) =
      (if within_int_bound (Unsigned m)
            (&(w2n (word_of_bytes_be bs:bytes32)))
       then INL (IntV (&(w2n (word_of_bytes_be bs:bytes32))))
       else INR (RuntimeError "convert BytesV uint bound")) /\
    evaluate_extract32 bs 0 (IntT m) =
      (if within_int_bound (Signed m) (w2i (word_of_bytes_be bs:bytes32))
       then INL (IntV (w2i (word_of_bytes_be bs:bytes32)))
       else INR (RuntimeError "convert BytesV int bound")) /\
    evaluate_extract32 bs 0 (BytesT (Fixed m)) =
      (if EVERY ($= 0w) (DROP m bs) then INL (BytesV (TAKE m bs))
       else INR (RuntimeError "evaluate_extract32 bytesM")) /\
    evaluate_extract32 bs 0 AddressT =
      (if EVERY ($= 0w) (TAKE 12 bs) then INL (BytesV (DROP 12 bs))
       else INR (RuntimeError "evaluate_extract32 address clamp"))
Proof
  rpt gen_tac >> disch_tac >>
  `TAKE 32 bs = bs` by metis_tac[TAKE_LENGTH_ID] >>
  `!w:bytes32. w >> 0 = w` by
    simp[fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA] >>
  simp[evaluate_extract32_def, evaluate_convert_def, PAD_LEFT, PAD_RIGHT]
QED

Theorem extract32_inbounds_slice:
  n + 32 <= LENGTH bs ==>
  LENGTH (TAKE 32 (DROP n bs)) = 32 /\
  evaluate_extract32 bs n bt = evaluate_extract32 (TAKE 32 (DROP n bs)) 0 bt
Proof
  strip_tac >>
  `LENGTH (TAKE 32 (DROP n bs)) = 32` by simp[LENGTH_TAKE_EQ] >>
  simp[evaluate_extract32_def, TAKE_TAKE]
QED

Theorem extract32_slice_encoding:
  LENGTH bs = 32 /\ extract32_result_base_ok bt /\
  evaluate_extract32 bs 0 bt = INL v ==>
  typed_val_to_w256 (BaseTV bt) v = (word_of_bytes_be bs:bytes32)
Proof
  strip_tac >>
  Cases_on `bt` >> gvs[extract32_result_base_ok_def, extract32_slice_guards]
  >- (gvs[AllCaseEqs(), typed_val_to_w256_def, val_to_w256_def,
          integer_wordTheory.i2w_def])
  >- (gvs[AllCaseEqs(), typed_val_to_w256_def, val_to_w256_def, i2w_w2i])
  >- (Cases_on `b` >> gvs[extract32_result_base_ok_def, extract32_slice_guards, AllCaseEqs()] >>
      irule extract32_fixed_encoding >> gvs[EVERY_MEM, EQ_SYM_EQ]) >>
  gvs[AllCaseEqs()] >> irule extract32_address_encoding >>
  gvs[EVERY_MEM, EQ_SYM_EQ]
QED
