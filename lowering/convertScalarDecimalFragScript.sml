Theory convertScalarDecimalFrag
Ancestors
  exprUnopStraight
  convertScalarDecimalRun convertScalarProps exprSimUnop exprSimConvert
  exprLowering compileEnv valueEncoding vyperValue vyperValueOperation
  vyperDecimalBounds integer integer_word words arithmeticProps intExtension
Libs
  intLib

Theorem scalar_int_decimal_frag:
  !ctx func cenv cx es0 sg bits i.
    0 < bits /\ bits <= 256 /\
    within_int_bound (if sg then Signed bits else Unsigned bits) i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (ConvIntToDecimal sg bits 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1)))
      (i2w i) (BaseT DecimalT)
      (convert_result cx (BaseT (if sg then IntT bits else UintT bits))
        (BaseT DecimalT) (IntV i)) es0
Proof
  rpt strip_tac >> irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def, bounded_decimal_op_def] >>
  Cases_on `within_int_bound decimal_bound (i * decimal_scale)` >> gvs[]
  >- (strip_tac >> qexists_tac `i2w (i * decimal_scale)` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >> drule_all (SRULE[decimal_scale_def] scalar_int_to_decimal_ok) >> simp[]) >>
  rpt strip_tac >> drule_all (SRULE[decimal_scale_def] scalar_int_to_decimal_abort) >> simp[]
QED

Theorem scalar_decimal_word_bounds:
  w2i (i2w (-&(2 ** 167)):bytes32) = -&(2 ** 167) /\
  w2i (i2w (&(2 ** 167 - 1)):bytes32) = &(2 ** 167 - 1)
Proof
  conj_tac
  >- (irule w2i_i2w_neg_pow2 >> simp[]) >>
  irule w2i_i2w_pow2_sub1 >> simp[]
QED

Theorem scalar_int_decimal_mk_op:
  mk_convert_op (BaseT (if sg then IntT bits else UintT bits)) (BaseT DecimalT) =
  ConvIntToDecimal sg bits 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1)
Proof
  Cases_on `sg` >>
  simp[mk_convert_op_def, type_bounds_def, type_bits_def,
       is_signed_type_def, is_bytestring_type_def, SRULE[] scalar_decimal_word_bounds]
QED

Theorem scalar_int_decimal_mk_frag:
  !ctx func cenv cx es0 sg bits i.
    0 < bits /\ bits <= 256 /\
    within_int_bound (if sg then Signed bits else Unsigned bits) i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (mk_convert_op (BaseT (if sg then IntT bits else UintT bits))
          (BaseT DecimalT)))
      (i2w i) (BaseT DecimalT)
      (convert_result cx (BaseT (if sg then IntT bits else UintT bits))
        (BaseT DecimalT) (IntV i)) es0
Proof
  rpt strip_tac >> simp[scalar_int_decimal_mk_op] >>
  irule (SRULE[] scalar_int_decimal_frag) >> simp[]
QED
Theorem scalar_decimal_signed_frag:
  !ctx func cenv cx es0 bits i.
    0 < bits /\ bits <= 256 /\ within_int_bound decimal_bound i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (ConvDecimalToInt 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1)
          (-&(2 ** (bits-1))) (&(2 ** (bits-1))-1) T))
      (i2w i) (BaseT (IntT bits))
      (convert_result cx (BaseT DecimalT) (BaseT (IntT bits)) (DecimalV i)) es0
Proof
  rpt strip_tac >>
  `-&(2 ** (bits-1)):int <= 0` by simp[] >>
  `0 <= (&(2 ** (bits-1)):int)-1` by
    (simp[INT_SUB_LE, INT_OF_NUM_LE]) >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def] >>
  Cases_on `-&(2 ** (bits-1)) * decimal_scale <= i /\
    i <= (&(2 ** (bits-1))-1) * decimal_scale` >> gvs[]
  >- (drule_all decimal_truncate_signed_bound >> strip_tac >>
      strip_tac >> qexists_tac `i2w (i quot decimal_scale)` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def,
           decimal_truncate_eq_quot] >>
      rpt strip_tac >>
      irule (SRULE[decimal_scale_def] scalar_decimal_to_int_ok) >> simp[] >>
      qexistsl_tac [`&(2 ** (bits-1))-1`, `-&(2 ** (bits-1))`, `x`] >>
      simp[]) >>
  rpt strip_tac >>
  irule (SRULE[decimal_scale_def] scalar_decimal_to_int_abort) >> simp[] >>
  qexistsl_tac [`&(2 ** (bits-1))-1`, `i`, `-&(2 ** (bits-1))`, `op`, `x`] >>
  simp[]
QED

Theorem scalar_decimal_unsigned_frag:
  !ctx func cenv cx es0 bits i.
    0 < bits /\ bits < 256 /\ within_int_bound decimal_bound i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (ConvDecimalToInt 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1)
          0 (&(2 ** bits)-1) T))
      (i2w i) (BaseT (UintT bits))
      (convert_result cx (BaseT DecimalT) (BaseT (UintT bits)) (DecimalV i)) es0
Proof
  rpt strip_tac >>
  `0 <= (&(2 ** bits):int)-1` by simp[INT_SUB_LE, INT_OF_NUM_LE] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def] >>
  Cases_on `0 <= i /\ i <= (&(2 ** bits)-1) * decimal_scale` >> gvs[]
  >- (drule_all decimal_div_unsigned_bound >> strip_tac >>
      `i quot decimal_scale = i / decimal_scale` by
        (simp[decimal_scale_def] >>
         rewrite_tac[GSYM decimal_truncate_eq_quot] >>
         `~(i < 0)` by intLib.ARITH_TAC >>
         Cases_on `i = 0` >> simp[SGN_def, INT_ABS]) >>
      strip_tac >> qexists_tac `i2w (i quot decimal_scale)` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >>
      qpat_x_assum `_ quot _ = _` (mp_tac o SRULE[decimal_scale_def]) >>
      disch_then (fn th => once_rewrite_tac[GSYM th]) >>
      irule (SRULE[decimal_scale_def] scalar_decimal_to_int_ok) >> simp[] >>
      qexistsl_tac [`&(2 ** bits)-1`, `0`, `x`] >> simp[]) >>
  rpt strip_tac >>
  irule (SRULE[decimal_scale_def] scalar_decimal_to_int_abort) >> simp[] >>
  qexistsl_tac [`&(2 ** bits)-1`, `i`, `0`, `op`, `x`] >> simp[]
QED

Theorem scalar_decimal_signed_mk_op:
  0 < bits /\ bits <= 256 ==>
  mk_convert_op (BaseT DecimalT) (BaseT (IntT bits)) =
  ConvDecimalToInt 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1)
    (-&(2 ** (bits-1))) (&(2 ** (bits-1))-1) T
Proof
  strip_tac >>
  `bits - 1 <= 255` by decide_tac >>
  `w2i (i2w (-&(2 ** (bits-1))):bytes32) = -&(2 ** (bits-1))` by
    (irule w2i_i2w_neg_pow2 >> simp[]) >>
  `w2i (i2w (&(2 ** (bits-1)-1)):bytes32) = &(2 ** (bits-1)-1)` by
    (irule w2i_i2w_pow2_sub1 >> simp[]) >>
  simp[mk_convert_op_def, type_bounds_def, type_bits_def,
       is_signed_type_def, is_bytestring_type_def, SRULE[] scalar_decimal_word_bounds] >>
  `0 < 2 ** (bits-1)` by simp[] >>
  simp[INT_SUB]
QED

Theorem scalar_decimal_signed_mk_frag:
  !ctx func cenv cx es0 bits i.
    0 < bits /\ bits <= 256 /\ within_int_bound decimal_bound i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (mk_convert_op (BaseT DecimalT) (BaseT (IntT bits))))
      (i2w i) (BaseT (IntT bits))
      (convert_result cx (BaseT DecimalT) (BaseT (IntT bits)) (DecimalV i)) es0
Proof
  rpt strip_tac >> simp[scalar_decimal_signed_mk_op] >>
  irule (SRULE[] scalar_decimal_signed_frag) >> gvs[]
QED

Theorem scalar_decimal_unsigned_mk_op:
  0 < bits /\ bits < 256 ==>
  mk_convert_op (BaseT DecimalT) (BaseT (UintT bits)) =
  ConvDecimalToInt 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1)
    0 (&(2 ** bits)-1) T
Proof
  strip_tac >>
  `w2i (n2w (2 ** bits-1):bytes32) = &(2 ** bits-1)` by
    (rewrite_tac[GSYM i2w_pos] >> irule w2i_i2w_pow2_sub1 >> decide_tac) >>
  simp[mk_convert_op_def, type_bounds_def, type_bits_def,
       is_signed_type_def, is_bytestring_type_def, SRULE[] scalar_decimal_word_bounds] >>
  `0 < 2 ** bits` by simp[] >> simp[INT_SUB, w2i_eq_w2n]
QED

Theorem scalar_decimal_unsigned_mk_frag:
  !ctx func cenv cx es0 bits i.
    0 < bits /\ bits < 256 /\ within_int_bound decimal_bound i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (mk_convert_op (BaseT DecimalT) (BaseT (UintT bits))))
      (i2w i) (BaseT (UintT bits))
      (convert_result cx (BaseT DecimalT) (BaseT (UintT bits)) (DecimalV i)) es0
Proof
  rpt strip_tac >> simp[scalar_decimal_unsigned_mk_op] >>
  irule (SRULE[] scalar_decimal_unsigned_frag) >> gvs[]
QED

Theorem scalar_decimal_uint256_upper:
  within_int_bound decimal_bound i ==>
  i <= (&(2 ** 167)-1) * decimal_scale /\
  i <= (&(2 ** 256)-1) * decimal_scale
Proof
  simp[within_int_bound_def] >> intLib.ARITH_TAC
QED

Theorem scalar_decimal_uint256_mk_frag:
  !ctx func cenv cx es0 i.
    within_int_bound decimal_bound i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (mk_convert_op (BaseT DecimalT) (BaseT (UintT 256))))
      (i2w i) (BaseT (UintT 256))
      (convert_result cx (BaseT DecimalT) (BaseT (UintT 256)) (DecimalV i)) es0
Proof
  rpt strip_tac >> drule scalar_decimal_uint256_upper >> strip_tac >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >>
  simp[mk_convert_op_def, type_bounds_def, type_bits_def,
       is_signed_type_def, is_bytestring_type_def, SRULE[] scalar_decimal_word_bounds] >>
  simp[straight_fresh_convert_scalar, convert_result_def,
       evaluate_convert_from_not_address_bytes, evaluate_convert_def] >>
  Cases_on `0 <= i` >> gvs[]
  >- (`within_int_bound (Unsigned 256) (i / 10000000000)` by
        (irule decimal_div_unsigned_bound >> gvs[]) >>
      `i quot 10000000000 = i / 10000000000` by
        (rewrite_tac[GSYM decimal_truncate_eq_quot] >>
         `~(i < 0)` by intLib.ARITH_TAC >>
         Cases_on `i = 0` >> simp[SGN_def, INT_ABS]) >>
      strip_tac >> qexists_tac `i2w (i quot 10000000000)` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >>
      qpat_x_assum `_ quot _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
      irule (SRULE[decimal_scale_def] scalar_decimal_to_int_ok) >> simp[] >>
      qexistsl_tac [`&(2 ** 167)-1`, `0`, `x`] >> gvs[]) >>
  rpt strip_tac >>
  irule (SRULE[decimal_scale_def] scalar_decimal_to_int_abort) >> simp[] >>
  qexistsl_tac [`&(2 ** 167)-1`, `i`, `0`, `op`, `x`] >> gvs[]
QED
