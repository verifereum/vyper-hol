Theory convertScalarEncoding
Ancestors
  convertScalarProps valueEncodingProofs cv_std byte words list rich_list
  arithmetic valueEncoding vyperValue moduleLoweringProps

Theorem scalar_fixed_encoding:
  !m bs. typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) =
    (word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32)
Proof
  simp[typed_val_to_w256_def]
QED

Theorem scalar_address_encoding:
  !bs. typed_val_to_w256 (BaseTV AddressT) (BytesV bs) =
    (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)
Proof
  simp[typed_val_to_w256_def]
QED

Theorem scalar_fixed_encoding_num:
  !bs:word8 list. LENGTH bs <= 32 ==>
    (word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) =
      n2w (256 ** (32 - LENGTH bs) * num_of_bytes (REVERSE bs))
Proof
  rpt strip_tac >>
  simp[word_of_bytes_be_eq_num_of_bytes, dividesTheory.compute_divides,
       be_bytes_thm, PAD_RIGHT, GSYM REPLICATE_GENLIST,
       TAKE_APPEND1, TAKE_LENGTH_TOO_LONG, REVERSE_APPEND,
       num_of_bytes_APPEND]
QED

Theorem scalar_address_encoding_num:
  !bs:word8 list. LENGTH bs <= 32 ==>
    (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32) =
      n2w (num_of_bytes (REVERSE bs))
Proof
  rpt strip_tac >>
  simp[word_of_bytes_be_eq_num_of_bytes, dividesTheory.compute_divides,
       be_bytes_thm, PAD_LEFT, GSYM REPLICATE_GENLIST,
       TAKE_APPEND1, TAKE_LENGTH_TOO_LONG, REVERSE_APPEND,
       num_of_bytes_APPEND]
QED

Theorem scalar_fixed_encoding_bound:
  !bs:word8 list. LENGTH bs <= 32 ==>
    256 ** (32 - LENGTH bs) * num_of_bytes (REVERSE bs) < 2 ** 256
Proof
  rpt strip_tac >>
  qspec_then `REVERSE bs` mp_tac num_of_bytes_lt >> simp[] >> strip_tac >>
  `256 ** (32 - LENGTH bs) * num_of_bytes (REVERSE bs) <
   256 ** (32 - LENGTH bs) * 256 ** LENGTH bs` by simp[] >>
  `256 ** (32 - LENGTH bs) * 256 ** LENGTH bs = 2 ** 256` by
    (rewrite_tac[GSYM EXP_ADD] >>
     `32 - LENGTH bs + LENGTH bs = 32` by decide_tac >> simp[]) >>
  qpat_x_assum `_ < _ * _` mp_tac >>
  asm_rewrite_tac[] >> simp[MULT_COMM]
QED

Theorem scalar_bounded_product_quotient:
  !a p M:num. 0 < p /\ a * p < M ==>
    (a * p MOD M) DIV p = a MOD M
Proof
  rpt strip_tac >>
  `a <= a * p` by
    (Cases_on `p` >> gvs[MULT_SUC]) >>
  `a < M` by decide_tac >>
  simp[LESS_MOD, MULT_DIV]
QED

Theorem scalar_fixed_shr:
  !bs:word8 list. LENGTH bs <= 32 ==>
    (word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) >>>
      (8 * (32 - LENGTH bs)) =
    word_of_bytes_be (PAD_LEFT 0w 32 bs)
Proof
  rpt strip_tac >>
  simp[scalar_fixed_encoding_num, scalar_address_encoding_num] >>
  ONCE_REWRITE_TAC[GSYM w2n_11] >>
  pure_rewrite_tac[w2n_lsr, w2n_n2w, dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  drule scalar_fixed_encoding_bound >> strip_tac >>
  `256 ** (32 - LENGTH bs) = 2 ** (8 * (32 - LENGTH bs))` by
    simp[EXP_EXP_MULT] >>
  asm_rewrite_tac[] >> irule scalar_bounded_product_quotient >>
  conj_tac >- simp[] >>
  qpat_x_assum `_ * _ < _` mp_tac >>
  asm_rewrite_tac[] >> simp[MULT_COMM]
QED

Theorem scalar_signed_scaled:
  !u b s. 0 < b /\ b + s = 256 /\ u < 2 ** b ==>
    w2i (n2w (u * 2 ** s):bytes32) =
    signed_int_mod b (&u) * &(2 ** s)
Proof
  rpt strip_tac >>
  `u * 2 ** s < 2 ** 256` by
    (qpat_x_assum `b + s = 256` (SUBST1_TAC o SYM) >>
     simp[EXP_ADD]) >>
  `2 ** (b - 1) * 2 ** s = 2 ** 255` by
    (rewrite_tac[GSYM EXP_ADD] >> AP_TERM_TAC >> decide_tac) >>
  `u * 2 ** s < 2 ** 255 <=> u < 2 ** (b - 1)` by
    (qpat_x_assum `_ * _ = 2 ** 255` (SUBST1_TAC o SYM) >> simp[]) >>
  pure_rewrite_tac[integer_wordTheory.w2i_eq_w2n, w2n_n2w,
    dimword_def, wordsTheory.INT_MIN_def,
    fcpLib.INDEX_CONV ``dimindex(:256)``, numeralTheory.numeral_sub] >>
  `u * 2 ** s MOD 2 ** 256 = u * 2 ** s` by metis_tac[LESS_MOD] >>
  asm_rewrite_tac[] >>
  simp[vyperValueOperationTheory.signed_int_mod_def, integerTheory.INT_MOD,
       LESS_MOD, integerTheory.INT_GE, integerTheory.INT_LT] >>
  Cases_on `u < 2 ** (b - 1)` >> gvs[] >>
  `2 ** b * 2 ** s = 2 ** 256` by
    (rewrite_tac[GSYM EXP_ADD] >> simp[]) >>
  simp[integerTheory.INT_SUB_RDISTRIB, integerTheory.INT_MUL,
       GSYM integerTheory.INT_OF_NUM]
QED

Theorem scalar_signed_sar_num:
  !u b s. 0 < b /\ b + s = 256 /\ u < 2 ** b ==>
    (n2w (u * 2 ** s):bytes32) >> s =
    i2w (signed_int_mod b (&u))
Proof
  rpt strip_tac >>
  `s < 256` by decide_tac >>
  `i2w (w2i (n2w (u * 2 ** s):bytes32) / (2:int) ** s) =
   (n2w (u * 2 ** s):bytes32) >> s` by
    (simp[integer_wordTheory.i2w_DIV, integer_wordTheory.w2i_ge,
          integer_wordTheory.w2i_le]) >>
  drule_all scalar_signed_scaled >> strip_tac >>
  qpat_x_assum `i2w _ = _` (SUBST1_TAC o SYM) >>
  asm_rewrite_tac[] >>
  simp[integerTheory.INT_POW, integerTheory.INT_DIV_RMUL]
QED

Theorem scalar_fixed_sar:
  !bs:word8 list. 0 < LENGTH bs /\ LENGTH bs <= 32 ==>
    (word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) >>
      (8 * (32 - LENGTH bs)) =
    i2w (signed_int_mod (8 * LENGTH bs) (&(num_of_bytes (REVERSE bs))))
Proof
  rpt strip_tac >>
  simp[scalar_fixed_encoding_num] >>
  `256 ** (32 - LENGTH bs) = 2 ** (8 * (32 - LENGTH bs))` by
    simp[EXP_EXP_MULT] >>
  `256 ** (32 - LENGTH bs) * num_of_bytes (REVERSE bs) =
   num_of_bytes (REVERSE bs) * 2 ** (8 * (32 - LENGTH bs))` by
    simp[MULT_COMM] >>
  asm_rewrite_tac[] >>
  irule scalar_signed_sar_num >> simp[] >>
  qspec_then `REVERSE bs` mp_tac num_of_bytes_lt >>
  simp[EXP_EXP_MULT]
QED

Theorem scalar_fixed_widen:
  !bs m. typed_val_to_w256 (BaseTV (BytesT (Fixed m)))
           (BytesV (PAD_RIGHT 0w m bs)) =
         typed_val_to_w256 (BaseTV (BytesT (Fixed (LENGTH bs)))) (BytesV bs)
Proof
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right,
       PAD_RIGHT, GSYM REPLICATE_GENLIST, byteTheory.word_of_bytes_be_def,
       word_of_bytes_append_zero]
QED

Theorem scalar_zero_bytes_replicate:
  !bs:word8 list. EVERY (\b. b = 0w) bs ==>
    bs = REPLICATE (LENGTH bs) 0w
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem scalar_fixed_narrow:
  !bs m. EVERY (\b. b = 0w) (DROP m bs) ==>
    typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV (TAKE m bs)) =
    typed_val_to_w256 (BaseTV (BytesT (Fixed (LENGTH bs)))) (BytesV bs)
Proof
  rpt strip_tac >>
  drule scalar_zero_bytes_replicate >> strip_tac >>
  `bs = TAKE m bs ++ REPLICATE (LENGTH (DROP m bs)) 0w` by
    metis_tac[TAKE_DROP] >>
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right] >>
  qpat_x_assum `bs = _ ++ _` (fn th => CONV_TAC (RHS_CONV (RAND_CONV (REWR_CONV th)))) >>
  simp[byteTheory.word_of_bytes_be_def, word_of_bytes_append_zero]
QED

Theorem scalar_num_of_bytes_zero:
  !bs:word8 list. num_of_bytes bs = 0 <=> EVERY (\b. b = 0w) bs
Proof
  Induct >> simp[num_of_bytes_def, w2n_eq_0, CONJ_COMM]
QED

Theorem scalar_fixed_zero:
  !bs:word8 list. LENGTH bs <= 32 ==>
    ((word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) = 0w <=>
      EVERY (\b. b = 0w) bs)
Proof
  rpt strip_tac >>
  drule scalar_fixed_encoding_bound >> strip_tac >>
  simp[scalar_fixed_encoding_num] >>
  ONCE_REWRITE_TAC[GSYM w2n_11] >>
  pure_rewrite_tac[w2n_n2w, dimword_def,
    fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  `256 ** (32 - LENGTH bs) * num_of_bytes (REVERSE bs) MOD 2 ** 256 =
   256 ** (32 - LENGTH bs) * num_of_bytes (REVERSE bs)` by
    metis_tac[LESS_MOD] >>
  gvs[MULT_COMM, scalar_num_of_bytes_zero, EVERY_REVERSE]
QED

Theorem scalar_reverse_split_num:
  !bs:word8 list. !n. n <= LENGTH bs ==>
    num_of_bytes (REVERSE bs) =
    num_of_bytes (REVERSE (DROP n bs)) +
    256 ** (LENGTH bs - n) * num_of_bytes (REVERSE (TAKE n bs))
Proof
  rpt strip_tac >>
  `bs = TAKE n bs ++ DROP n bs` by simp[] >>
  qpat_x_assum `bs = _ ++ _` (fn th =>
    CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV th))))) >>
  simp[REVERSE_APPEND, num_of_bytes_APPEND]
QED

Theorem scalar_fixed_drop_shift:
  !bs:word8 list. !n. n <= LENGTH bs /\ LENGTH bs <= 32 ==>
    (word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) << (8 * n) =
    word_of_bytes_be (PAD_RIGHT 0w 32 (DROP n bs))
Proof
  rpt strip_tac >>
  Cases_on `n = 32`
  >- (gvs[] >> `LENGTH bs = 32` by decide_tac >>
      simp[DROP_LENGTH_TOO_LONG, word_lsl_n2w,
           scalar_fixed_encoding_num, num_of_bytes_def]) >>
  `n < 32` by decide_tac >>
  drule_all scalar_reverse_split_num >> strip_tac >>
  simp[scalar_fixed_encoding_num, word_lsl_n2w] >>
  `2 ** (8 * n) = 256 ** n` by simp[EXP_EXP_MULT] >>
  `256 ** (32 - LENGTH bs) * 256 ** n =
   256 ** (32 - (LENGTH bs - n))` by
    (rewrite_tac[GSYM EXP_ADD] >> AP_TERM_TAC >> decide_tac) >>
  `256 ** (32 - LENGTH bs) * 256 ** (LENGTH bs - n) * 256 ** n =
   dimword (:256)` by
    (rewrite_tac[GSYM EXP_ADD, dimword_def] >>
     `32 - LENGTH bs + (LENGTH bs - n) + n = 32` by decide_tac >> simp[]) >>
  asm_rewrite_tac[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
  `n + 32 - LENGTH bs = 32 - (LENGTH bs - n)` by decide_tac >>
  `num_of_bytes (REVERSE (DROP n bs)) * 256 ** n * 256 ** (32 - LENGTH bs) =
   num_of_bytes (REVERSE (DROP n bs)) * 256 ** (32 - (LENGTH bs - n))` by
    (qpat_x_assum `_ * _ = 256 ** _` (SUBST1_TAC o SYM) >>
     CONV_TAC (AC_CONV (MULT_ASSOC, MULT_COMM))) >>
  `num_of_bytes (REVERSE (TAKE n bs)) * 256 ** (LENGTH bs - n) * 256 ** n *
   256 ** (32 - LENGTH bs) =
   num_of_bytes (REVERSE (TAKE n bs)) * dimword (:256)` by
    (qpat_x_assum `_ = dimword _` (SUBST1_TAC o SYM) >>
     CONV_TAC (AC_CONV (MULT_ASSOC, MULT_COMM))) >>
  asm_rewrite_tac[] >> simp[NoAsms, Once MOD_PLUS, MOD_EQ_0]
QED

Theorem scalar_fixed_narrow_test:
  !bs:word8 list. !n. n <= LENGTH bs /\ LENGTH bs <= 32 ==>
    ((word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) << (8 * n) = 0w <=>
     EVERY (\b. b = 0w) (DROP n bs))
Proof
  rpt strip_tac >>
  simp[scalar_fixed_drop_shift, scalar_fixed_zero]
QED

Theorem scalar_word_to_fixed:
  !w:bytes32. !m. m <= 32 ==>
    typed_val_to_w256 (BaseTV (BytesT (Fixed m)))
      (BytesV (DROP (32 - m) (word_to_bytes_be w))) =
    w << (8 * (32 - m))
Proof
  rpt strip_tac >>
  qspecl_then [`word_to_bytes_be w`, `32 - m`] mp_tac scalar_fixed_drop_shift >>
  simp[byteTheory.word_to_bytes_be_def, byteTheory.LENGTH_word_to_bytes,
       typed_val_to_w256_def, word_of_bytes_be_pad_right,
       byteTheory.word_of_bytes_be_def, byteTheory.word_of_bytes_word_to_bytes,
       dividesTheory.compute_divides]
QED

Theorem scalar_address_to_fixed:
  !bs:word8 list. !m. LENGTH bs <= m /\ m <= 32 ==>
    typed_val_to_w256 (BaseTV (BytesT (Fixed m)))
      (BytesV (PAD_LEFT 0w m bs)) =
    typed_val_to_w256 (BaseTV AddressT) (BytesV bs) << (8 * (32 - m))
Proof
  rpt strip_tac >>
  Cases_on `m = 0`
  >- (gvs[] >> simp[typed_val_to_w256_def, scalar_fixed_encoding_num,
                    scalar_address_encoding_num, PAD_LEFT, num_of_bytes_def, ZERO_SHIFT]) >>
  `LENGTH bs <= 32 /\ 8 * (32 - m) < 256` by decide_tac >>
  simp[typed_val_to_w256_def, scalar_fixed_encoding_num,
       scalar_address_encoding_num, word_lsl_n2w,
       PAD_LEFT, REVERSE_APPEND, GSYM REPLICATE_GENLIST,
       num_of_bytes_APPEND, EXP_EXP_MULT, MULT_COMM]
QED

Theorem scalar_flag_encoding:
  !k m. typed_val_to_w256 (FlagTV k) (FlagV m) = n2w m /\
    typed_val_to_w256 (BaseTV (UintT 256)) (IntV (&m)) = n2w m /\
    typed_val_to_w256 (BaseTV (IntT 256)) (IntV (&m)) = n2w m
Proof
  simp[typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_pos]
QED

Theorem scalar_flag_encoding_num:
  !k m. m < 2 ** 256 ==>
    w2n (typed_val_to_w256 (FlagTV k) (FlagV m)) = m
Proof
  rpt strip_tac >>
  gvs[scalar_flag_encoding, w2n_n2w, dimword_def]
QED

Theorem scalar_flag_to_bytes32:
  !k m. typed_val_to_w256 (BaseTV (BytesT (Fixed 32)))
    (BytesV (word_to_bytes_be (n2w m:bytes32))) =
    typed_val_to_w256 (FlagTV k) (FlagV m)
Proof
  simp[typed_val_to_w256_def, val_to_w256_def, word_of_bytes_be_pad_right,
       byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes, dividesTheory.compute_divides]
QED

Theorem scalar_address_zero:
  !bs:word8 list. LENGTH bs <= 32 ==>
    ((word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32) = 0w <=>
     EVERY (\b. b = 0w) bs)
Proof
  rpt strip_tac >>
  qspec_then `REVERSE bs` mp_tac num_of_bytes_lt >> simp[] >> strip_tac >>
  `num_of_bytes (REVERSE bs) < 2 ** 256` by
    (irule LESS_LESS_EQ_TRANS >> qexists_tac `256 ** LENGTH bs` >> simp[]) >>
  simp[scalar_address_encoding_num] >>
  ONCE_REWRITE_TAC[GSYM w2n_11] >>
  pure_rewrite_tac[w2n_n2w, dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  `num_of_bytes (REVERSE bs) MOD 2 ** 256 = num_of_bytes (REVERSE bs)` by
    metis_tac[LESS_MOD] >>
  asm_rewrite_tac[] >> simp[scalar_num_of_bytes_zero, EVERY_REVERSE]
QED
