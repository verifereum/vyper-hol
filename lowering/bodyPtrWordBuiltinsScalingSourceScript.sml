(* Source classification for a word operand of AsWeiValue. *)
Theory bodyPtrWordBuiltinsScalingSource
Ancestors exprSimWordBuiltins exprSimWordArgs vyperContext
  vyperAST vyperState words venomExecSemantics integer_word vyperTypeBuiltins

Theorem word_scale_source_words:
  builtin_result cx ac ann (AsWeiValue d) ts [IntV (&w2n (w:bytes32))] =
    if w2n w * denomination_multiplier d < dimword (:256) then
      INL (IntV (&(w2n w * denomination_multiplier d)))
    else INR (Error (RuntimeError "ewv bound"))
Proof
  simp[builtin_result_def, evaluate_builtin_def, evaluate_as_wei_value_uint,
       dimword_def, integerTheory.INT_OF_NUM_MUL, integerTheory.INT_LT] >>
  IF_CASES_TAC >> simp[]
QED
