Theory convertScalarDecimal
Ancestors
  convertScalarEncoding convertScalarProps exprSimConvert exprSimUnop
  vyperValue vyperValueOperation vyperArith integer arithmetic words integer_word
  venomExecSemantics vyperDecimalBounds intExtension
Libs
  intLib

Theorem scalar_decimal_prescale:
  !i. within_int_bound decimal_bound (i * decimal_scale) <=>
    (-&(2 ** 167)) quot decimal_scale <= i /\
    i <= (&(2 ** 167) - 1) quot decimal_scale
Proof
  simp[within_int_bound_def] >> intLib.ARITH_TAC
QED

Theorem scalar_decimal_sdiv:
  !i. within_int_bound decimal_bound i ==>
    safe_sdiv (i2w i) (n2w 10000000000) =
    (i2w (i quot decimal_scale):bytes32)
Proof
  rpt strip_tac >> simp[safe_sdiv_def, word_quot] >>
  `w2i (i2w i:bytes32) = i` by
    (irule w2i_i2w_within_signed >> qexists_tac `168` >> gvs[]) >>
  simp[dimword_def, w2i_eq_w2n, word_msb_n2w, w2n_n2w, wordsTheory.INT_MIN_def]
QED

Theorem scalar_decimal_sdiv_signed:
  !i. within_int_bound decimal_bound i ==>
    safe_sdiv (i2w i) (n2w 10000000000) =
    (i2w (SGN i * (ABS i / decimal_scale)):bytes32)
Proof
  simp[decimal_truncate_eq_quot, scalar_decimal_sdiv]
QED

Theorem scalar_decimal_sdiv_unsigned:
  !i. within_int_bound decimal_bound i /\ 0 <= i ==>
    safe_sdiv (i2w i) (n2w 10000000000) =
    (i2w (i / decimal_scale):bytes32)
Proof
  rpt strip_tac >> drule scalar_decimal_sdiv_signed >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  Cases_on `i = 0` >> simp[SGN_def, INT_ABS]
QED

Theorem scalar_conditional_interval:
  !a b i l h:int. a <= i /\ i <= b ==>
    (((if a < l then l <= i else T) /\
      (if b > h then i <= h else T)) <=> (l <= i /\ i <= h))
Proof
  rpt strip_tac >> rpt IF_CASES_TAC >> simp[] >> intLib.ARITH_TAC
QED

Theorem scalar_signed_lower_endpoint:
  !a l. within_int_bound (Signed 256) a /\ a < l /\ l <= 0 ==>
    within_int_bound (Signed 256) l
Proof
  simp[within_int_bound_def] >> intLib.ARITH_TAC
QED

Theorem scalar_signed_upper_endpoint:
  !b h. within_int_bound (Signed 256) b /\ 0 <= h /\ h < b ==>
    within_int_bound (Signed 256) h
Proof
  simp[within_int_bound_def] >> intLib.ARITH_TAC
QED

Theorem scalar_unsigned_upper_endpoint:
  !b h. within_int_bound (Unsigned 256) b /\ 0 <= h /\ h < b ==>
    within_int_bound (Unsigned 256) h
Proof
  simp[within_int_bound_def] >> intLib.ARITH_TAC
QED

Theorem scalar_decimal_prescale_endpoints:
  within_int_bound (Signed 256) ((-&(2 ** 167)) quot decimal_scale) /\
  within_int_bound (Signed 256) ((&(2 ** 167) - 1) quot decimal_scale) /\
  within_int_bound (Unsigned 256) ((&(2 ** 167) - 1) quot decimal_scale) /\
  (-&(2 ** 167)) quot decimal_scale <= 0 /\
  0 <= (&(2 ** 167) - 1) quot decimal_scale
Proof
  EVAL_TAC
QED

Theorem scalar_decimal_scaled_lower_endpoint:
  !l. l <= 0 /\ -&(2 ** 167) < l * decimal_scale ==>
    within_int_bound (Signed 256) (l * decimal_scale)
Proof
  rpt strip_tac >> irule scalar_signed_lower_endpoint >>
  conj_tac >- (gvs[decimal_scale_def] >> intLib.ARITH_TAC) >>
  qexists_tac `-&(2 ** 167)` >>
  simp[within_int_bound_def] >>
  gvs[decimal_scale_def] >> intLib.ARITH_TAC
QED

Theorem scalar_decimal_scaled_upper_endpoint:
  !h. 0 <= h /\ h * decimal_scale < &(2 ** 167) - 1 ==>
    within_int_bound (Signed 256) (h * decimal_scale)
Proof
  rpt strip_tac >> irule scalar_signed_upper_endpoint >>
  conj_tac >- (gvs[decimal_scale_def] >> intLib.ARITH_TAC) >>
  qexists_tac `&(2 ** 167) - 1` >>
  simp[within_int_bound_def] >>
  gvs[decimal_scale_def] >> intLib.ARITH_TAC
QED
