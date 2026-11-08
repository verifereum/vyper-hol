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
