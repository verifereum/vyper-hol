Theory bodyPtrTypeBuiltinsBytesWordParts
Ancestors
  bodyPtrTypeBuiltinsUintCounted bodyPtrSignedConvertBool
  exprLowering exprLoweringProps emitHelperProps compileEnv

(* All positive-capacity branches share exactly the SHR loader. *)
Theorem bytes_word_convert_parts:
  (conv = ConvBytestringToBool \/ (?m. conv = ConvBytestringToBytesM m) \/
    (?b n. conv = ConvBytestringToInt F b n)) /\
  compile_type_convert x conv sa = (out,sb) ==>
  ?word bits sm. load_bytestring_as_word x SHR sa = ((word,bits),sm) /\
    (conv = ConvBytestringToBool ==> compile_type_convert word ConvToBool sm = (out,sb)) /\
    (!m. conv = ConvBytestringToBytesM m ==> emit_op SHL [bits;word] sm = (out,sb)) /\
    (!b n. conv = ConvBytestringToInt F b n ==>
      if n*8 > b then compile_int_clamp F b word sm = (out,sb)
      else out = word /\ sb = sm)
Proof
  strip_tac >> gvs[] >>
  fs[compile_type_convert_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `a` >> gvs[comp_bind_def, comp_return_def] >>
  Cases_on `8*n > b` >> gvs[comp_return_def]
QED
