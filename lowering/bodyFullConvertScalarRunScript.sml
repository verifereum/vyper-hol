(* Physical scalar conversion runs, independent of horizons and ghosts. *)
Theory bodyFullConvertScalarRun
Ancestors
  exprSimConvert convertScalarBytesRun convertScalarEncoding convertScalarFlags
  convertScalarBytes convertScalarOutputs convertScalarDecimalFrag
  bodyPtrTypeBuiltinsIntegerSemantic bodyPtrTypeBuiltinsScalarArithmetic
  exprUnopStraight exprSimUnop exprLoweringProps exprLowering
  vyperTyping vyperValue vyperValueOperation compileEnv vyperAST vyperTypeSystem
  venomExecSemantics venomState freshWrites emitHelperProps emitHelper
  integer_word words arithmeticProps list rich_list finite_map convertScalarProps

Theorem scalar_source_word_types[local]:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  IS_SOME (evaluate_type tenv src) /\ IS_SOME (evaluate_type tenv dst) ==>
  is_word_type src /\ is_word_type dst /\ ~is_bytestring_type dst
Proof
  Cases_on `src` >> Cases_on `dst` >>
  gvs[valid_conversion_def, is_bytestring_type_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def] >>
  Cases_on `b` >> gvs[valid_conversion_def, is_bytestring_type_def,
                      is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  Cases_on `b'` >> gvs[valid_conversion_def, is_bytestring_type_def,
                       is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  rpt (FIRST [Cases_on `b''`, Cases_on `b`] >>
       gvs[valid_conversion_def, is_bytestring_type_def,
           is_word_type_def, vyperValueTheory.evaluate_type_def])
QED

Theorem scalar_source_dispatch_partition[local]:
  valid_conversion src dst /\ ~is_bytestring_type src ==>
  case (case dst of FlagT name =>
          ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
        | _ => mk_convert_op src dst) of
    ConvToBool => T
  | ConvIntToInt _ _ _ _ => T
  | ConvBytesToInt _ _ _ => T
  | ConvIntToBytesM _ _ _ => T
  | ConvIntToDecimal _ _ _ _ _ => T
  | ConvDecimalToInt _ _ _ _ _ _ => T
  | ConvBoolToDecimal _ => T
  | ConvBytesMToDecimal _ _ _ _ => T
  | ConvToAddress => T
  | ConvBytesToAddress _ => T
  | ConvToFlag _ => T
  | ConvBytesMToBytesM _ _ => T
  | ConvIdentity => T
  | _ => F
Proof
  Cases_on `dst` >>
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `b` >> simp[mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `src` >>
  gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def] >>
  Cases_on `b` >>
  gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def] >>
  rpt (FIRST [Cases_on `b'`, Cases_on `b''`] >>
       gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def]) >>
  simp[type_bounds_def, type_bits_def, is_signed_type_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem scalar_dispatch_straight_fresh[local]:
  valid_conversion src dst /\ ~is_bytestring_type src ==>
  straight_fresh (compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst))
Proof
  strip_tac >> drule_all scalar_source_dispatch_partition >>
  disch_then (qspec_then `cenv` mp_tac) >>
  qmatch_goalsub_abbrev_tac `straight_fresh (compile_type_convert x conv)` >>
  Cases_on `conv` >> simp[straight_fresh_convert, straight_fresh_convert_scalar] >>
  simp[compile_type_convert_def, straight_fresh_return]
QED

(* Fixed bytes0 is represented by a zero word.  In particular SAR 256 is
   defined, so this case does not need a dynamic buffer loader. *)
Theorem scalar_fixed_zero_value[local]:
  value_has_type (BaseTV (BytesT (Fixed 0))) v ==>
  v = BytesV [] /\ typed_val_to_w256 (BaseTV (BytesT (Fixed 0))) v = 0w
Proof
  Cases_on `v` >> simp[value_has_type_def] >> strip_tac >> gvs[] >>
  EVAL_TAC >> simp[]
QED

Theorem scalar_fixed_zero_signed_result[local]:
  convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT (IntT b)) (BytesV []) = INL (IntV 0) /\
  convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT DecimalT) (BytesV []) = INL (DecimalV 0)
Proof
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []):bytes32 = 0w` by
    (EVAL_TAC >> simp[]) >>
  `((0w:bytes32) >> 256) = 0w` by wordsLib.WORD_DECIDE_TAC >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       within_int_bound_def, bounded_decimal_op_def, w2i_def,
       word_msb_def, word_0] >> Cases_on `0 < b` >> simp[]
QED

Theorem scalar_fixed_zero_int_raw[local]:
  compile_type_convert x (ConvBytesToInt 0 sg b) sa = (r,sb) /\
  eval_operand x ss = SOME 0w /\ fresh_vars_wrt sa ss /\ b <= 256 ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\ eval_operand r sf = SOME 0w
Proof
  Cases_on `sg` >> strip_tac >>
  `((0w:bytes32) >> w2n (n2w ((32-0)*8):bytes32)) = 0w` by
    (simp[] >> wordsLib.WORD_DECIDE_TAC) >>
  drule scalar_bytes_int_word_ok >>
  disch_then (qspecl_then [`ss`,`0w:bytes32`] mp_tac) >>
  simp[arithmeticPropsTheory.in_type_range_def, type_bits_def, is_signed_type_def, w2i_def,
       word_msb_def, word_0]
QED

Theorem scalar_fixed_zero_decimal_raw[local]:
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed 0))) (BaseT DecimalT)) sa = (r,sb) /\
  eval_operand x ss = SOME 0w /\ fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\ eval_operand r sf = SOME 0w
Proof
  simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
       type_bits_def, is_signed_type_def, w2i_i2w] >>
  rewrite_tac[SRULE [] scalar_bytes_decimal_eq] >> strip_tac >>
  irule scalar_fixed_zero_int_raw >> simp[] >> qexistsl_tac [`168`,`T`,`x`] >> gvs[scalar_bytes_decimal_eq, compile_type_convert_def]
QED
