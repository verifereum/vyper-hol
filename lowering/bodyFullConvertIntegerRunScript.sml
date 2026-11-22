(* Integer-source physical conversion execution only. *)
Theory bodyFullConvertIntegerRun
Ancestors
  bodyPtrTypeBuiltinsIntegerSemantic convertScalarOutputs convertScalarFlags
  convertScalarDecimalRun convertScalarEncoding exprSimConvert exprLowering
  exprLoweringProps compileEnv vyperValue vyperValueOperation vyperTypeSystem
  vyperAST venomExecSemantics venomState emitHelperProps emitHelper
  words integer_word arithmeticProps list finite_map valueEncoding vyperTyping

Theorem scalar_integer_source_run:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ fresh_vars_wrt sa s /\ ~s.vs_halted /\
  (?sg bits. src = BaseT (if sg then IntT bits else UintT bits)) ==>
  case convert_result cx src dst v of
    INL vout => ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (typed_val_to_w256 tout vout)
  | INR exc => (?msg. exc = Error (RuntimeError msg)) /\
      ?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t
Proof
  strip_tac >> Cases_on `sg` >> gvs[] >>
  Cases_on `dst` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def]
  >- (Cases_on `b` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def]
      >- (drule_at (Pat `compile_type_convert _ _ _ = _`)
            (SRULE [] (Q.INST [`si` |-> `T`, `so` |-> `F`] scalar_integer_typed_actual)) >>
          simp[vyperValueTheory.evaluate_type_def] >>
          disch_then (qspecl_then [`v`,`s`,`cx`] mp_tac) >> simp[] >> strip_tac >> Cases_on `convert_result cx (BaseT (IntT bits)) (BaseT (UintT n)) v` >> gvs[] >> metis_tac[])
      >- (drule_at (Pat `compile_type_convert _ _ _ = _`)
            (SRULE [] (Q.INST [`si` |-> `T`, `so` |-> `T`] scalar_integer_typed_actual)) >>
          simp[vyperValueTheory.evaluate_type_def] >>
          disch_then (qspecl_then [`v`,`s`,`cx`] mp_tac) >> simp[] >> strip_tac >> Cases_on `convert_result cx (BaseT (IntT bits)) (BaseT (IntT n)) v` >> gvs[] >> metis_tac[])
      >- (Cases_on `v` >> gvs[value_has_type_def, convert_result_def,
            evaluate_convert_from_not_address_bytes, evaluate_convert_def,
            typed_val_to_w256_def, val_to_w256_def, mk_convert_op_def, is_bytestring_type_def] >>
          drule_all convert_bool_run >> strip_tac >>
          Cases_on `i = 0` >- simp[bool_to_word_def, i2w_0] >>
          `i2w i <> (0w:bytes32)` by
            (strip_tac >> drule_all (SRULE [] (Q.SPECL [`bits`,`T`] exprSimArithTheory.i2w_eq_0_within)) >> simp[]) >>
          simp[bool_to_word_def])
      >- suspend "signed_decimal"
      >> suspend "signed_bytes")
  >- suspend "unsigned_base"
  >> suspend "flag"
QED

Resume scalar_integer_source_run[signed_decimal]:
  Cases_on `v` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def,
    mk_convert_op_def, is_bytestring_type_def, type_bounds_def, type_bits_def,
    is_signed_type_def, w2i_i2w, INT_MIN_def, INT_MAX_def, dimword_def] >>
  gvs[integer_wordTheory.w2i_i2w, integer_wordTheory.INT_MIN,
      integer_wordTheory.INT_MAX, wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
      wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  `0 < bits` by decide_tac >>
  Cases_on `within_int_bound decimal_bound (i * decimal_scale)`
  >- (drule_all (SIMP_RULE std_ss [integerTheory.INT_SUB,
        EVAL ``(-&(2 ** 167):int)``, EVAL ``(&(2 ** 167):int) - 1``]
          (Q.SPEC `T` scalar_int_to_decimal_ok)) >> strip_tac >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes,
        evaluate_convert_def, bounded_decimal_op_def, typed_val_to_w256_def, val_to_w256_def] >>
      metis_tac[]) >>
  drule_all (SIMP_RULE std_ss [integerTheory.INT_SUB,
    EVAL ``(-&(2 ** 167):int)``, EVAL ``(&(2 ** 167):int) - 1``]
      (Q.SPEC `T` scalar_int_to_decimal_abort)) >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
    evaluate_convert_def, bounded_decimal_op_def] >> metis_tac[]
QED
Resume scalar_integer_source_run[signed_bytes]:
  Cases_on `b'` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def,
    mk_convert_op_def, is_bytestring_type_def] >>
  drule_all scalar_int_bytes_run >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
    evaluate_convert_def, scalar_word_to_fixed]
QED
Resume scalar_integer_source_run[unsigned_base]:
  Cases_on `b` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def]
  >- suspend "uint_uint"
  >- suspend "uint_int"
  >- suspend "uint_bool"
  >- suspend "uint_decimal"
  >- suspend "uint_bytes"
  >> suspend "uint_address"
QED
Resume scalar_integer_source_run[flag]:
  gvs[AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  `within_int_bound (Unsigned 256) i` by simp[within_int_bound_def] >>
  Cases_on `Num i < 2 ** (cenv.ce_flag_n_members (nsid_to_string p))`
  >- (drule_all scalar_to_flag_run_ok >> strip_tac >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes,
        evaluate_convert_def, typed_val_to_w256_def, val_to_w256_def,
        integer_wordTheory.i2w_pos] >>
      `i = &Num i` by intLib.ARITH_TAC >>
      qpat_x_assum `i = &Num i` SUBST1_TAC >> simp[integer_wordTheory.i2w_pos]) >>
  drule_all scalar_to_flag_run_abort >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
    evaluate_convert_def] >> metis_tac[]
QED
Resume scalar_integer_source_run[uint_uint]:
  drule_at (Pat `compile_type_convert _ _ _ = _`)
    (SRULE [] (Q.INST [`si` |-> `F`, `so` |-> `F`] scalar_integer_typed_actual)) >>
  simp[vyperValueTheory.evaluate_type_def] >>
  disch_then (qspecl_then [`v`,`s`,`cx`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `convert_result cx (BaseT (UintT bits)) (BaseT (UintT n)) v` >> gvs[] >> metis_tac[]
QED
Resume scalar_integer_source_run[uint_int]:
  drule_at (Pat `compile_type_convert _ _ _ = _`)
    (SRULE [] (Q.INST [`si` |-> `F`, `so` |-> `T`] scalar_integer_typed_actual)) >>
  simp[vyperValueTheory.evaluate_type_def] >>
  disch_then (qspecl_then [`v`,`s`,`cx`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `convert_result cx (BaseT (UintT bits)) (BaseT (IntT n)) v` >> gvs[] >> metis_tac[]
QED
Resume scalar_integer_source_run[uint_bool]:
  Cases_on `v` >> gvs[value_has_type_def, convert_result_def,
    evaluate_convert_from_not_address_bytes, evaluate_convert_def,
    typed_val_to_w256_def, val_to_w256_def, mk_convert_op_def, is_bytestring_type_def] >>
  `within_int_bound (Unsigned bits) i` by simp[within_int_bound_def] >>
  drule_all convert_bool_run >> strip_tac >>
  Cases_on `i = 0` >- simp[bool_to_word_def, i2w_0] >>
  `i2w i <> (0w:bytes32)` by
    (strip_tac >> drule_all (SRULE [] (Q.SPECL [`bits`,`F`] exprSimArithTheory.i2w_eq_0_within)) >> simp[]) >>
  simp[bool_to_word_def]
QED
Resume scalar_integer_source_run[uint_decimal]:
  Cases_on `v` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def,
    mk_convert_op_def, is_bytestring_type_def, type_bounds_def, type_bits_def,
    is_signed_type_def, w2i_i2w, INT_MIN_def, INT_MAX_def, dimword_def] >>
  gvs[integer_wordTheory.w2i_i2w, integer_wordTheory.INT_MIN,
      integer_wordTheory.INT_MAX, wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
      wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  `within_int_bound (Unsigned bits) i` by simp[within_int_bound_def] >>
  Cases_on `within_int_bound decimal_bound (i * decimal_scale)`
  >- (drule_all (SIMP_RULE std_ss [integerTheory.INT_SUB,
        EVAL ``(-&(2 ** 167):int)``, EVAL ``(&(2 ** 167):int) - 1``]
          (Q.SPEC `F` scalar_int_to_decimal_ok)) >> strip_tac >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes,
        evaluate_convert_def, bounded_decimal_op_def, typed_val_to_w256_def, val_to_w256_def] >>
      metis_tac[]) >>
  drule_all (SIMP_RULE std_ss [integerTheory.INT_SUB,
    EVAL ``(-&(2 ** 167):int)``, EVAL ``(&(2 ** 167):int) - 1``]
      (Q.SPEC `F` scalar_int_to_decimal_abort)) >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
    evaluate_convert_def, bounded_decimal_op_def] >> metis_tac[]
QED
Resume scalar_integer_source_run[uint_bytes]:
  Cases_on `b'` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def,
    mk_convert_op_def, is_bytestring_type_def] >>
  drule_all scalar_int_bytes_run >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
    evaluate_convert_def, scalar_word_to_fixed]
QED
Resume scalar_integer_source_run[uint_address]:
  Cases_on `v` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def,
    mk_convert_op_def, is_bytestring_type_def] >>
  `within_int_bound (Unsigned bits) i` by simp[within_int_bound_def] >>
  drule (SRULE [] (Q.INST [`si` |-> `F`, `so` |-> `F`, `bo` |-> `160`]
    scalar_integer_actual_run)) >>
  disch_then (qspecl_then [`s`, `i`] mp_tac) >> simp[] >>
  Cases_on `within_int_bound (Unsigned 160) i` >> simp[] >> strip_tac
  >- (simp[convert_result_def, evaluate_convert_from_not_address_bytes,
        evaluate_convert_def, convertScalarBytesTheory.scalar_typed_address_word] >>
      `0 <= i /\ i < &(2**160)` by fs[within_int_bound_ineq] >>
      `i = &Num i` by intLib.ARITH_TAC >>
      `Num i < 2**160` by (fs[] >> intLib.ARITH_TAC) >>
      qpat_x_assum `i = &Num i` SUBST1_TAC >>
      simp[integer_wordTheory.i2w_pos, wordsTheory.w2w_def,
        wordsTheory.w2n_n2w, wordsTheory.dimword_def,
        fcpLib.INDEX_CONV ``dimindex(:160)``] >> fs[]) >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
    evaluate_convert_def] >> metis_tac[]

QED
Finalise scalar_integer_source_run
