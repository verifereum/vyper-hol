(* Current source semantics for the formerly excluded empty fixed operand. *)
Theory bodyMemTbConvertScalarAudit
Ancestors
  exprSimConvert convertScalarEncoding vyperValueOperation integer_word words
  fcp byte list valueEncoding vyperTyping vyperValue

Theorem convert_fixed0_int_result:
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

Theorem convert_fixed0_decimal_result:
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
