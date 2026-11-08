Theory bodyPtrBytestringBuiltinsOpcodeBuiltins
Ancestors bodyPtrBytestringBuiltinsOpcodeScalars
          bodyPtrBytestringBuiltinsOpcodeArithmetic
          bodyPtrBytestringBuiltinsOpcodeCalldata
          supportedExprForms supportedTypes compileEnv

(* The source-supported Bop cases never enter the array membership or
   bytestring hashing paths, so the scalar binop interface is sufficient. *)
Theorem supported_binop_scalar_paths:
  supported_binop opr ty rhs lb ne ==>
    opr <> In /\ opr <> NotIn /\
    ~(is_bytestring_type ty /\ (opr = Eq \/ opr = NotEq))
Proof
  Cases_on `opr` >> simp[supported_binop_def] >>
  Cases_on `ty` >> simp[supported_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT sz` >> Cases_on `sz` >>
  simp[supported_word_type_def, is_bytestring_type_def]
QED
