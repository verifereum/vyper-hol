(* Decimal and Bool source physical conversion execution. *)
Theory bodyFullConvertDecimalRun
Ancestors
  convertScalarDecimalRun convertScalarEncoding convertScalarOutputs
  exprSimConvert exprLowering exprLoweringProps compileEnv vyperValue
  vyperValueOperation vyperTypeSystem vyperTyping vyperAST valueEncoding
  venomExecSemantics venomState emitHelperProps emitHelper
  integer_word words arithmeticProps list finite_map vyperDecimalBounds

Theorem scalar_decimal_bool_source_run:
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
  (src = BaseT DecimalT \/ src = BaseT BoolT) ==>
  case convert_result cx src dst v of
    INL vout => ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (typed_val_to_w256 tout vout)
  | INR exc => (?msg. exc = Error (RuntimeError msg)) /\
      ?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t
Proof
  strip_tac >> gvs[]
  >- (Cases_on `dst` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def] >>
      Cases_on `b` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def]
      >- suspend "uint" >> suspend "int") >>
  Cases_on `dst` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def] >>
  Cases_on `b` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def]
  >- suspend "bool_uint" >> suspend "bool_int"
QED
Resume scalar_decimal_bool_source_run[uint]:
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `n = 256`
  >- suspend "uint256" >>
  `0 < n /\ n < 256` by decide_tac >>
  gvs[mk_convert_op_def, type_bounds_def, type_bits_def, is_signed_type_def,
      is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def,
      arithmeticPropsTheory.w2i_i2w_pow2_sub1, integerTheory.INT_SUB] >>
  `w2i (n2w (2 ** n-1):bytes32) = &(2 ** n-1)` by
    (rewrite_tac[GSYM integer_wordTheory.i2w_pos] >>
     irule arithmeticPropsTheory.w2i_i2w_pow2_sub1 >> decide_tac) >>
  gvs[SRULE [] (Q.SPEC `167` arithmeticPropsTheory.w2i_i2w_neg_pow2),
      SRULE [] (Q.SPEC `167` arithmeticPropsTheory.w2i_i2w_pow2_sub1),
      EVAL ``w2i (0w:bytes32)``] >>
  `0 < 2 ** n` by simp[] >> gvs[integerTheory.INT_SUB] >>
  `0 <= (&(2**n):int)-1` by simp[integerTheory.INT_SUB_LE, integerTheory.INT_OF_NUM_LE] >>
  Cases_on `0 <= i /\ i <= (&(2**n)-1) * decimal_scale`
  >- (drule_at (Pat `compile_type_convert _ _ _ = _`)
        (SIMP_RULE std_ss [integerTheory.INT_SUB] scalar_decimal_to_int_ok) >>
      disch_then (qspecl_then [`i`,`s`] mp_tac) >>
      (impl_tac >- gvs[decimal_scale_def, integerTheory.INT_SUB]) >> strip_tac >>
      `i quot decimal_scale = i / decimal_scale` by
        (simp[decimal_scale_def] >> rewrite_tac[GSYM decimal_truncate_eq_quot] >>
         `~(i < 0)` by metis_tac[integerTheory.INT_NOT_LT] >>
         Cases_on `i = 0` >> simp[intExtensionTheory.SGN_def, integerTheory.INT_ABS]) >>
      qspecl_then [`n`,`i`] mp_tac (GEN_ALL decimal_div_unsigned_bound) >>
      simp[] >> strip_tac >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
           typed_val_to_w256_def, val_to_w256_def] >>
      gvs[decimal_scale_def, integerTheory.INT_SUB] >> metis_tac[]) >>
  drule_at (Pat `compile_type_convert _ _ _ = _`)
    (SIMP_RULE std_ss [integerTheory.INT_SUB] scalar_decimal_to_int_abort) >>
  disch_then (qspecl_then [`i`,`s`] mp_tac) >>
  simp[integerTheory.INT_SUB, decimal_scale_def] >> strip_tac >>
  gvs[decimal_scale_def, integerTheory.INT_SUB] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       decimal_scale_def, integerTheory.INT_SUB] >> metis_tac[]
QED
Resume scalar_decimal_bool_source_run[int]:
  Cases_on `v` >> gvs[value_has_type_def] >>
  `n - 1 <= 255` by decide_tac >>
  gvs[mk_convert_op_def, type_bounds_def, type_bits_def, is_signed_type_def,
      is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def,
      arithmeticPropsTheory.w2i_i2w_neg_pow2, arithmeticPropsTheory.w2i_i2w_pow2_sub1,
      integerTheory.INT_SUB] >>
  gvs[SRULE [] (Q.SPEC `167` arithmeticPropsTheory.w2i_i2w_neg_pow2),
      SRULE [] (Q.SPEC `167` arithmeticPropsTheory.w2i_i2w_pow2_sub1)] >>
  `0 < 2 ** (n-1)` by simp[] >> gvs[integerTheory.INT_SUB] >>
  `0 < n` by decide_tac >>
  `-&(2**(n-1)):int <= 0` by simp[] >>
  `0 <= (&(2**(n-1)):int)-1` by simp[integerTheory.INT_SUB_LE, integerTheory.INT_OF_NUM_LE] >>
  Cases_on `-&(2**(n-1)) * decimal_scale <= i /\ i <= (&(2**(n-1))-1) * decimal_scale`
  >- (drule_at (Pat `compile_type_convert _ _ _ = _`)
        (SIMP_RULE std_ss [integerTheory.INT_SUB] scalar_decimal_to_int_ok) >>
      disch_then (qspecl_then [`i`,`s`] mp_tac) >> simp[] >> strip_tac >>
      qspecl_then [`n`,`i`] mp_tac (GEN_ALL decimal_truncate_signed_bound) >>
      simp[] >> strip_tac >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
          typed_val_to_w256_def, val_to_w256_def, decimal_truncate_eq_quot,
          decimal_scale_def] >> gvs[decimal_scale_def, integerTheory.INT_SUB] >> metis_tac[]) >>
  drule_at (Pat `compile_type_convert _ _ _ = _`)
    (SIMP_RULE std_ss [integerTheory.INT_SUB] scalar_decimal_to_int_abort) >>
  disch_then (qspecl_then [`i`,`s`] mp_tac) >>
  simp[integerTheory.INT_SUB, decimal_scale_def] >> strip_tac >>
  gvs[decimal_scale_def, integerTheory.INT_SUB] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       decimal_scale_def, integerTheory.INT_SUB] >> metis_tac[]
QED
Resume scalar_decimal_bool_source_run[bool_uint]:
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `b` >>
  gvs[mk_convert_op_def, compile_type_convert_def, emitted_insts_def,
      run_inst_seq_def, convert_result_def, evaluate_convert_from_not_address_bytes,
      evaluate_convert_def, typed_val_to_w256_def, val_to_w256_def,
      within_int_bound_def, comp_return_def] >> EVAL_TAC
QED
Resume scalar_decimal_bool_source_run[bool_int]:
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `b` >>
  gvs[mk_convert_op_def, compile_type_convert_def, emitted_insts_def,
      run_inst_seq_def, convert_result_def, evaluate_convert_from_not_address_bytes,
      evaluate_convert_def, typed_val_to_w256_def, val_to_w256_def,
      within_int_bound_def, comp_return_def] >> EVAL_TAC
QED
Resume scalar_decimal_bool_source_run[uint256]:
  gvs[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def,
      type_bounds_def, type_bits_def, is_signed_type_def,
      SRULE [] (Q.SPEC `167` arithmeticPropsTheory.w2i_i2w_neg_pow2),
      SRULE [] (Q.SPEC `167` arithmeticPropsTheory.w2i_i2w_pow2_sub1)] >>
  `i <= (&(2**167)-1) * decimal_scale /\ i <= (&(2**256)-1) * decimal_scale` by
    (fs[within_int_bound_ineq] >> intLib.ARITH_TAC) >>
  Cases_on `0 <= i`
  >- (drule_at (Pat `compile_type_convert _ _ _ = _`)
        (SIMP_RULE std_ss [integerTheory.INT_SUB] scalar_decimal_to_int_ok) >>
      disch_then (qspecl_then [`i`,`s`] mp_tac) >>
      (impl_tac >- gvs[decimal_scale_def]) >> strip_tac >>
      `within_int_bound (Unsigned 256) (i / 10000000000)` by
        (irule decimal_div_unsigned_bound >> gvs[]) >>
      `i quot 10000000000 = i / 10000000000` by
        (rewrite_tac[GSYM decimal_truncate_eq_quot] >>
         `~(i < 0)` by metis_tac[integerTheory.INT_NOT_LT] >>
         Cases_on `i = 0` >> simp[intExtensionTheory.SGN_def, integerTheory.INT_ABS]) >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
           typed_val_to_w256_def, val_to_w256_def] >>
      gvs[decimal_scale_def] >> metis_tac[]) >>
  drule_at (Pat `compile_type_convert _ _ _ = _`)
    (SIMP_RULE std_ss [integerTheory.INT_SUB] scalar_decimal_to_int_abort) >>
  disch_then (qspecl_then [`i`,`s`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def] >> metis_tac[]
QED
Finalise scalar_decimal_bool_source_run
