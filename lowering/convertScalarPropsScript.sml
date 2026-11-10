Theory convertScalarProps
Ancestors
  exprUnopStraight
  exprSimConvert exprSimUnop exprLowering freshWrites emitHelper
  compileEnv vyperValue valueEncoding vyperValueOperation
  venomExecSemantics exprLoweringProps words integer_word arithmetic

val scalar_sf_step = FIRST [
  irule straight_fresh_bind >> conj_tac,
  irule straight_fresh_ignore_bind >> conj_tac,
  gen_tac >> BETA_TAC,
  irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
  irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
  MATCH_ACCEPT_TAC straight_fresh_return,
  IF_CASES_TAC];

Theorem straight_fresh_convert_scalar:
  !x m sg bits out_s out_b divisor lo hi ilo ihi n.
    straight_fresh (compile_type_convert x (ConvBytesToInt m sg bits)) /\
    straight_fresh (compile_type_convert x (ConvIntToBytesM sg bits m)) /\
    straight_fresh (compile_type_convert x (ConvIntToDecimal sg bits divisor lo hi)) /\
    straight_fresh (compile_type_convert x (ConvDecimalToInt divisor ilo ihi lo hi sg)) /\
    straight_fresh (compile_type_convert x (ConvBoolToDecimal divisor)) /\
    straight_fresh (compile_type_convert x ConvToAddress) /\
    straight_fresh (compile_type_convert x (ConvBytesToAddress m)) /\
    straight_fresh (compile_type_convert x (ConvToFlag n)) /\
    straight_fresh (compile_type_convert x (ConvBytesMToDecimal m divisor lo hi)) /\
    straight_fresh (compile_type_convert x (ConvBytesMToBytesM m n))
Proof
  rw[compile_type_convert_def, compile_int_clamp_def] >> rpt scalar_sf_step
QED

Theorem scalar_bytes32_identity_frag:
  !ctx func cenv cx bs es0.
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesMToBytesM 32 32))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs))
      (BaseT (BytesT (Fixed 32))) (INL (BytesV bs)) es0
Proof
  rpt gen_tac >> irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >>
  strip_tac >>
  qexists_tac `typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)` >>
  simp[evaluate_type_def, compile_type_convert_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> simp[emitted_insts_def, run_inst_seq_def]
QED

Theorem scalar_bytes0_bool_frag:
  !ctx func cenv cx es0.
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x ConvToBool)
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 0))) (BytesV []))
      (BaseT BoolT) (INL (BoolV F)) es0
Proof
  rpt gen_tac >> irule unop_frag_straight >>
  simp[straight_fresh_convert, is_word_type_def] >> strip_tac >>
  qexists_tac `0w` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  rpt strip_tac >> drule_all convert_bool_run >>
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []) = (0w:bytes32)` by
    (EVAL_TAC >> simp[]) >>
  simp[bool_to_word_def]
QED

Theorem scalar_bytes32_identity_result:
  !cx bs. LENGTH bs = 32 ==>
    convert_result cx (BaseT (BytesT (Fixed 32)))
      (BaseT (BytesT (Fixed 32))) (BytesV bs) = INL (BytesV bs)
Proof
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  rpt strip_tac >> simp[listTheory.PAD_RIGHT]
QED

Theorem scalar_bytes0_bool_result:
  !cx. convert_result cx (BaseT (BytesT (Fixed 0)))
    (BaseT BoolT) (BytesV []) = INL (BoolV F)
Proof
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def]
QED

Theorem scalar_bytes0_encoding:
  typed_val_to_w256 (BaseTV (BytesT (Fixed 0))) (BytesV []) = (0w:bytes32)
Proof
  simp[typed_val_to_w256_def, val_to_w256_def] >> EVAL_TAC >> simp[]
QED

Theorem scalar_bytes0_int_result:
  !cx b. 1 < b /\ b <= 256 ==>
    convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT (IntT b))
      (BytesV []) = INL (IntV 0)
Proof
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []) = (0w:bytes32)` by
    (EVAL_TAC >> simp[]) >>
  `word_asr (0w:bytes32) 256 = 0w` by
    simp[fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA,
         word_msb_def, word_0] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       within_int_bound_def, w2i_def]
QED

Theorem scalar_bytes0_decimal_result:
  !cx. convert_result cx (BaseT (BytesT (Fixed 0)))
    (BaseT DecimalT) (BytesV []) = INL (DecimalV 0)
Proof
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []) = (0w:bytes32)` by
    (EVAL_TAC >> simp[]) >>
  `word_asr (0w:bytes32) 256 = 0w` by
    simp[fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA,
         word_msb_def, word_0] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       bounded_decimal_op_def, w2i_def] >> EVAL_TAC
QED
