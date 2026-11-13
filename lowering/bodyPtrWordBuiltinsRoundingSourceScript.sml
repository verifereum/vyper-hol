(* Source arithmetic classification for the two decimal rounding branches. *)
Theory bodyPtrWordBuiltinsRoundingSource
Ancestors exprSimWordBuiltins exprSimWordArgs exprSimDefs vyperContext vyperValue valueEncoding
  integer_word words

Theorem word_round_source:
  builtin_result cx acc ann (if up then Ceil else Floor) ts [DecimalV i] =
    INL (IntV ((if up then i + (10000000000 - 1) else i) / 10000000000))
Proof
  Cases_on `up` >> simp[builtin_result_def, evaluate_builtin_def, decimal_scale_def]
QED

Theorem word_round_decimal_result:
  within_int_bound (Signed 168) i ==>
  safe_sdiv (if word_lt (i2w i : bytes32) 0w then
      (if up then i2w i else i2w i - n2w (10000000000-1))
    else (if up then i2w i + n2w (10000000000-1) else i2w i))
    (n2w 10000000000) =
  i2w ((if up then i + (10000000000-1) else i) / 10000000000)
Proof
  Cases_on `up` >> simp[] >> strip_tac
  >- (drule decimal_ceil_word >> simp[WORD_LTi, word_0_w2i]) >>
  drule decimal_floor_word >> simp[WORD_LTi, word_0_w2i]
QED
