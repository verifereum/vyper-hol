Theory bodyPtrTypeBuiltinsBytesWordTypes
Ancestors exprLowering exprLoweringProps vyperAST vyperTyping vyperTypeSystem
  vyperValue arithmetic compileEnv

(* One complete partition, including the signed destinations for reuse. *)
Theorem bytestring_scalar_type_partition:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst ==>
  (?n. src = BaseT (BytesT (Dynamic n)) /\
    ((dst = BaseT BoolT /\ n <= 32) \/
     (?b. dst = BaseT (UintT b) /\ n <= 32) \/
     (?b. dst = BaseT (IntT b) /\ n <= 32) \/
     (dst = BaseT AddressT /\ n <= 32) \/
     (dst = BaseT DecimalT /\ n <= 32) \/
     (?m. dst = BaseT (BytesT (Fixed m)) /\ n <= m))) \/
  (?n m. src = BaseT (StringT n) /\ dst = BaseT (BytesT (Fixed m)) /\ n <= m)
Proof
  Cases_on `src` >> Cases_on `dst` >>
  gvs[is_bytestring_type_def, valid_conversion_def] >>
  Cases_on `b` >> gvs[is_bytestring_type_def, valid_conversion_def] >>
  Cases_on `b'` >> gvs[is_bytestring_type_def, valid_conversion_def] >>
  rpt (FIRST [Cases_on `b''`, Cases_on `b`] >>
       gvs[is_bytestring_type_def, valid_conversion_def])
QED

Theorem bytestring_scalar_unsigned_convert_op:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  well_formed_type tenv dst ==>
  is_word_type dst /\
  (mk_convert_op src dst = ConvBytestringToBool \/
   (?m. mk_convert_op src dst = ConvBytestringToBytesM m) \/
   (?b n. mk_convert_op src dst = ConvBytestringToInt F b n))
Proof
  strip_tac >> drule_all bytestring_scalar_type_partition >> strip_tac >>
  gvs[mk_convert_op_def, is_bytestring_type_def, is_word_type_def,
      well_formed_type_def, evaluate_type_def]
QED
