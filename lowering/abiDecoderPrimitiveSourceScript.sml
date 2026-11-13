(* Arbitrary scalar source interpretation boundaries. *)
Theory abiDecoderPrimitiveSource
Ancestors
  abiDecoderSourceFacts abiDecoderSigned convertScalarEncoding
  abiDecoderClamp valueEncoding venomExecSemantics integer_word words
  arithmetic list rich_list byte contractABI exprSimArith convertScalarBytesRun exprSimConvert vyperArith
  vyperValueOperation vyperABI vyperValue convertScalarBytes
  abiDecoderCoherence vyperTypeSystem exprLowering
Libs
  intLib

Theorem abi_decoder_fixed_padding_clamp:
  LENGTH (bs:byte list) = 32 /\ 0 < m /\ m <= 32 ==>
  (((word_of_bytes T (0w:bytes32) bs) << w2n (n2w (m*8):bytes32) = 0w) <=>
    EVERY ((=) 0w) (DROP m bs))
Proof
  strip_tac >>
  `m*8 < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `m <= LENGTH bs /\ LENGTH bs <= 32` by simp[] >>
  drule_all scalar_fixed_drop_shift >>
  simp[byteTheory.word_of_bytes_be_def, PAD_RIGHT] >>
  strip_tac >>
  `LENGTH (DROP m bs) <= 32` by simp[] >>
  drule scalar_fixed_zero >>
  simp[byteTheory.word_of_bytes_be_def, w2n_n2w, MULT_COMM,
       PAD_RIGHT, LENGTH_DROP] >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_decoder_fixed_source_acceptance:
  LENGTH (bs:byte list) = 32 /\ 0 < m /\ m <= 32 ==>
  (vyper_decode_valid_enc (Bytes (SOME m)) bs <=>
   abi_decoder_clamp_valid (if m = 32 then NoClamp else BytesMClamp m)
     (word_of_bytes T (0w:bytes32) bs))
Proof
  strip_tac >> drule abi_decode_word_validation >> strip_tac >>
  Cases_on `m = 32`
  >- gvs[abi_decoder_clamp_valid_def, DROP_LENGTH_TOO_LONG] >>
  simp[abi_decoder_clamp_valid_def] >>
  drule_all abi_decoder_fixed_padding_clamp >>
  simp[w2n_n2w] >> metis_tac[]
QED

Theorem abi_decoder_unsigned_source_acceptance:
  LENGTH (bs:byte list) = 32 /\ valid_int_bound n ==>
  (vyper_decode_valid_enc (Uint n) bs <=>
   abi_decoder_clamp_valid (if n = 256 then NoClamp else IntClamp n F)
     (word_of_bytes T (0w:bytes32) bs))
Proof
  strip_tac >> drule abi_decode_word_validation >> strip_tac >>
  `n <= 256` by fs[valid_int_bound_def] >>
  Cases_on `n = 256`
  >- (gvs[abi_decoder_clamp_valid_def] >>
      mp_tac (Q.ISPEC `word_of_bytes T (0w:bytes32) bs` w2n_lt) >>
      simp[dimword_def]) >>
  simp[abi_decoder_clamp_valid_def]
QED

Theorem abi_decoder_bool_address_source_acceptance:
  LENGTH (bs:byte list) = 32 ==>
  (vyper_decode_valid_enc Bool bs <=>
   abi_decoder_clamp_valid BoolClamp (word_of_bytes T (0w:bytes32) bs)) /\
  (vyper_decode_valid_enc Address bs <=>
   abi_decoder_clamp_valid (IntClamp 160 F) (word_of_bytes T (0w:bytes32) bs))
Proof
  strip_tac >> drule abi_decode_word_validation >>
  simp[abi_decoder_clamp_valid_def]
QED

Theorem abi_decoder_signed_bound_source:
  0 < n ==> (int_bits_bound i n <=> within_int_bound (Signed n) i)
Proof
  strip_tac >> simp[int_bits_bound_def, within_int_bound_ineq] >>
  Cases_on `i < 0`
  >- (`?k. i = -&k` by (irule integerTheory.NUM_NEGINT_EXISTS >> intLib.ARITH_TAC) >>
      gvs[] >> Cases_on `k` >> gvs[] >> intLib.ARITH_TAC) >>
  `?k. i = &k` by (irule integerTheory.NUM_POSINT_EXISTS >> intLib.ARITH_TAC) >>
  gvs[] >> intLib.ARITH_TAC
QED

Theorem abi_decoder_signed_word_clamp:
  0 < n /\ n <= 256 /\ n MOD 8 = 0 ==>
  ((sign_extend (n2w (n DIV 8 - 1)) (w:bytes32) = w) <=>
   int_bits_bound (w2i w) n)
Proof
  strip_tac >> simp[abi_decoder_signed_bound_source] >>
  eq_tac
  >- (strip_tac >>
      Cases_on `n = 256`
      >- (gvs[within_int_bound_ineq] >>
          mp_tac (Q.ISPEC `w:bytes32` w2i_le) >>
          mp_tac (Q.ISPEC `w:bytes32` w2i_ge) >>
          simp[wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def] >>
          intLib.ARITH_TAC) >>
      `n = n DIV 8 * 8` by
        (`0 < 8n` by simp[] >> drule DIVISION >>
         disch_then (qspec_then `n` mp_tac) >> simp[]) >>
      `n DIV 8 - 1 <= 30 /\ 8 * (n DIV 8 - 1 + 1) = n` by
        (qpat_x_assum `sign_extend _ _ = _` kall_tac >>
         qpat_x_assum `n MOD 8 = 0` kall_tac >>
         qmatch_goalsub_abbrev_tac `d - 1` >>
         qpat_x_assum `Abbrev _` kall_tac >> intLib.ARITH_TAC) >>
      qspecl_then [`n DIV 8 - 1`, `w2i w`] mp_tac
        i2w_signed_int_mod_sign_extend >>
      simp[] >> strip_tac >>
      `within_int_bound (Signed n) (signed_int_mod n (w2i w))` by
        (irule scalar_signed_mod_bound >> simp[]) >>
      `within_int_bound (Signed 256) (signed_int_mod n (w2i w))` by
        (irule (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` scalar_int_bound_mono)) >>
         qexists_tac `n` >> simp[]) >>
      `w2i (i2w (signed_int_mod n (w2i w)):bytes32) =
       signed_int_mod n (w2i w)` by
        (irule w2i_i2w_within_signed >> qexists_tac `n` >> simp[]) >>
      metis_tac[]) >>
  strip_tac >>
  `valid_int_bound n` by simp[valid_int_bound_def] >>
  drule_all abi_decoder_signed_canonical_i2w >> simp[]
QED

Theorem abi_decoder_signed_source_acceptance:
  LENGTH (bs:byte list) = 32 /\ valid_int_bound n ==>
  (vyper_decode_valid_enc (Int n) bs <=>
   abi_decoder_clamp_valid (if n = 256 then NoClamp else IntClamp n T)
     (word_of_bytes T (0w:bytes32) bs))
Proof
  strip_tac >> drule abi_decode_word_validation >> strip_tac >>
  `0 < n /\ n <= 256 /\ n MOD 8 = 0` by fs[valid_int_bound_def] >>
  drule_all abi_decoder_signed_word_clamp >>
  disch_then (qspec_then `word_of_bytes T (0w:bytes32) bs` mp_tac) >>
  Cases_on `n = 256`
  >- (gvs[abi_decoder_clamp_valid_def, sign_extend_def, w2n_n2w, dimword_def]) >>
  simp[abi_decoder_clamp_valid_def] >> metis_tac[]
QED

Theorem abi_decoder_scalar_conversion:
  LENGTH (bs:byte list) = 32 /\ 0 < n ==>
  abi_to_vyper env (BaseT (UintT n)) (dec (Uint n) bs) =
    (if w2n (word_of_bytes T (0w:bytes32) bs) < 2 ** n
     then SOME (vyperValue$IntV (&(w2n (word_of_bytes T (0w:bytes32) bs))))
     else NONE) /\
  abi_to_vyper env (BaseT (IntT n)) (dec (Int n) bs) =
    (if int_bits_bound (w2i (word_of_bytes T (0w:bytes32) bs)) n
     then SOME (vyperValue$IntV (w2i (word_of_bytes T (0w:bytes32) bs)))
     else NONE) /\
  abi_to_vyper env (BaseT DecimalT) (dec (Int 168) bs) =
    (if int_bits_bound (w2i (word_of_bytes T (0w:bytes32) bs)) 168
     then SOME (DecimalV (w2i (word_of_bytes T (0w:bytes32) bs)))
     else NONE)
Proof
  strip_tac >> drule abi_decode_word_dec >> strip_tac >>
  simp[check_IntV_def, within_int_bound_ineq,
       abi_decoder_signed_bound_source]
QED

Theorem abi_decoder_flag_source_acceptance:
  LENGTH (bs:byte list) = 32 /\ FLOOKUP env nsid = SOME (FlagArgs m) /\
  m <= 256 ==>
  ((vyper_decode_valid_enc (Uint 256) bs /\
    ?v. abi_to_vyper env (FlagT nsid) (dec (Uint 256) bs) = SOME v) <=>
   abi_decoder_clamp_valid (if m = 256 then NoClamp else IntClamp m F)
     (word_of_bytes T (0w:bytes32) bs))
Proof
  strip_tac >>
  drule abi_decode_word_dec >> strip_tac >>
  drule abi_decode_word_validation >> strip_tac >>
  drule abi_decode_flag_conversion >> strip_tac >>
  `w2n (word_of_bytes T (0w:bytes32) bs) < 2 ** 256` by
    (mp_tac (Q.ISPEC `word_of_bytes T (0w:bytes32) bs` w2n_lt) >>
     simp[dimword_def]) >>
  Cases_on `m = 256` >>
  simp[abi_decoder_clamp_valid_def, valid_int_bound_def] >>
  Cases_on `w2n (word_of_bytes T (0w:bytes32) bs) < 2 ** m` >> gvs[]
QED

Theorem abi_decoder_numeric_converted_word:
  (abi_to_vyper env (BaseT (UintT n)) (NumV (w2n (w:bytes32))) = SOME v ==>
   typed_val_to_w256 (BaseTV (UintT n)) v = w) /\
  (abi_to_vyper env (BaseT (IntT n)) (contractABI$IntV (w2i w)) = SOME v ==>
   typed_val_to_w256 (BaseTV (IntT n)) v = w) /\
  (abi_to_vyper env (BaseT DecimalT) (contractABI$IntV (w2i w)) = SOME v ==>
   typed_val_to_w256 (BaseTV DecimalT) v = w) /\
  (FLOOKUP env nsid = SOME (FlagArgs m) /\
   abi_to_vyper env (FlagT nsid) (NumV (w2n w)) = SOME v ==>
   val_to_w256 v = w)
Proof
  simp[check_IntV_def, abi_to_vyper_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[typed_val_to_w256_def, val_to_w256_def]
QED

Theorem abi_decoder_fixed_converted_word:
  LENGTH (bs:byte list) = 32 /\
  vyper_decode_valid_enc (Bytes (SOME m)) bs /\
  abi_to_vyper env (BaseT (BytesT (Fixed m))) (dec (Bytes (SOME m)) bs) = SOME v ==>
  typed_val_to_w256 (BaseTV (BytesT (Fixed m))) v =
    word_of_bytes T (0w:bytes32) bs
Proof
  strip_tac >> drule abi_decode_word_validation >> strip_tac >>
  drule abi_decode_word_dec >> strip_tac >>
  gvs[abi_to_vyper_def, AllCaseEqs()] >>
  `EVERY (\b. b = 0w) (DROP m bs)` by fs[EVERY_MEM] >>
  drule scalar_fixed_narrow >>
  simp[typed_val_to_w256_def, byteTheory.word_of_bytes_be_def, PAD_RIGHT]
QED

Theorem abi_decoder_bool_converted_word:
  abi_to_vyper env (BaseT BoolT) (NumV (w2n (w:bytes32))) = SOME v ==>
  typed_val_to_w256 (BaseTV BoolT) v = w
Proof
  simp[abi_to_vyper_def, AllCaseEqs()] >> strip_tac >>
  `w2n w = 0 \/ w2n w = 1` by decide_tac >>
  gvs[typed_val_to_w256_def, val_to_w256_def] >>
  qpat_x_assum `w2n w = 1`
    (mp_tac o AP_TERM ``n2w:num -> bytes32``) >>
  pure_rewrite_tac[wordsTheory.n2w_w2n] >> strip_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_address_converted_word:
  abi_to_vyper env (BaseT AddressT) (NumV (w2n (w:bytes32))) = SOME v ==>
  typed_val_to_w256 (BaseTV AddressT) v = w
Proof
  simp[abi_to_vyper_def, AllCaseEqs()] >> strip_tac >>
  gvs[scalar_typed_address_word, within_int_bound_ineq,
      wordsTheory.w2w_def, wordsTheory.w2n_n2w, dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem abi_decoder_primitive_source_word:
  LENGTH (bs:byte list) = 32 /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\ abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v ==>
  typed_val_to_w256 tv v = word_of_bytes T (0w:bytes32) bs
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[type_to_abi_dec_info_def, abi_decoder_coherent_base_iff,
      abi_decoder_coherent_flag_iff]
  >- (Cases_on `b` >>
      gvs[abi_decode_scalar_descriptors, TAKE_LENGTH_TOO_LONG]
      >- (irule (cj 1 abi_decoder_numeric_converted_word) >> simp[])
      >- (irule (cj 2 abi_decoder_numeric_converted_word) >> simp[])
      >- (irule abi_decoder_bool_converted_word >> simp[])
      >- (irule (cj 3 abi_decoder_numeric_converted_word) >> simp[])
      >- (Cases_on `b'` >> gvs[abi_decode_scalar_descriptors] >>
          irule abi_decoder_fixed_converted_word >> simp[]) >>
      irule abi_decoder_address_converted_word >> simp[])
  >- (Cases_on `b` >> gvs[exprLoweringTheory.type_to_abi_dec_info_def])
  >- gvs[abi_decoder_coherent_struct_iff,
         exprLoweringTheory.type_to_abi_dec_info_def]
  >- (drule abi_decode_word_dec >> strip_tac >>
      gvs[typed_val_to_w256_def, val_to_w256_def]) >>
  gvs[assignable_type_def, well_formed_type_def, evaluate_type_def,
      Once abi_decoder_coherent_cases]
QED

Theorem abi_decoder_primitive_source_acceptance:
  LENGTH (bs:byte list) = 32 /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\ abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  ((vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v) <=>
   abi_decoder_clamp_valid clamp (word_of_bytes T (0w:bytes32) bs))
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[type_to_abi_dec_info_def, abi_decoder_coherent_base_iff,
      abi_decoder_coherent_flag_iff]
  >- (Cases_on `b` >> gvs[abi_decode_scalar_descriptors]
      >- (`valid_int_bound n` by
            fs[assignable_type_def, well_formed_type_def, evaluate_type_def,
               valid_int_bound_def, AllCaseEqs()] >>
          drule_all abi_decoder_unsigned_source_acceptance >> strip_tac >>
          drule abi_decode_word_validation >> strip_tac >>
          simp[check_IntV_def, within_int_bound_ineq, TAKE_LENGTH_TOO_LONG] >>
          Cases_on `w2n (word_of_bytes T (0w:bytes32) bs) < 2 ** n` >> gvs[])
      >- (`valid_int_bound n` by
            fs[assignable_type_def, well_formed_type_def, evaluate_type_def,
               valid_int_bound_def, AllCaseEqs()] >>
          `0 < n` by fs[valid_int_bound_def] >>
          drule_all abi_decoder_signed_source_acceptance >> strip_tac >>
          drule abi_decode_word_validation >> strip_tac >>
          simp[check_IntV_def, GSYM abi_decoder_signed_bound_source,
               TAKE_LENGTH_TOO_LONG] >>
          Cases_on `int_bits_bound (w2i (word_of_bytes T (0w:bytes32) bs)) n` >> gvs[])
      >- (drule abi_decoder_bool_address_source_acceptance >>
          simp[TAKE_LENGTH_TOO_LONG, abi_decoder_clamp_valid_def] >>
          metis_tac[])
      >- (`valid_int_bound 168` by simp[valid_int_bound_def] >>
          drule_all abi_decoder_signed_source_acceptance >> strip_tac >>
          drule abi_decode_word_validation >> strip_tac >>
          gvs[abi_decoder_signed_bound_source, TAKE_LENGTH_TOO_LONG])
      >- (Cases_on `b'` >> gvs[abi_decode_scalar_descriptors] >>
          `0 < n /\ n <= 32` by
            fs[abi_decode_bytes_widths_def, assignable_type_def,
               well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
          drule_all abi_decoder_fixed_source_acceptance >> strip_tac >>
          drule abi_decode_word_dec >> strip_tac >>
          gvs[abi_to_vyper_def, LENGTH_TAKE, compatible_bound_def])
      >> drule abi_decoder_bool_address_source_acceptance >>
      drule abi_decode_word_validation >>
      simp[TAKE_LENGTH_TOO_LONG, within_int_bound_ineq,
           abi_decoder_clamp_valid_def] >> metis_tac[])
  >- (Cases_on `b` >> gvs[exprLoweringTheory.type_to_abi_dec_info_def])
  >- gvs[abi_decoder_coherent_struct_iff,
         exprLoweringTheory.type_to_abi_dec_info_def]
  >- (drule_all abi_decoder_flag_source_acceptance >>
      drule abi_decode_word_dec >> strip_tac >>
      drule abi_decode_flag_conversion >>
      simp[TAKE_LENGTH_TOO_LONG]) >>
  gvs[assignable_type_def]
QED
