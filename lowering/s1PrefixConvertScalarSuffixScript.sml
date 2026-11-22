(* Request-prefix companion to bodyFullConvertScalarSuffix. *)
Theory s1PrefixConvertScalarSuffix
Ancestors
  s1PrefixPreds bodyFullConvertScalarSuffix s1PrefixDefs

Theorem zero_convert_prefix_outcome:
  is_bytestring_type src /\
  is_word_type dst /\
  valid_conversion src dst /\
  well_formed_type (get_tenv cx) dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  value_has_type tv v /\
  (v = BytesV [] \/ v = StringV []) /\
  ~s.vs_halted ==>
  gas_prefix_full (DF,lo,explicit,ctx,fn,PG)
      cx st0 (\st. (convert_result cx src dst v,st))
      (ee,s,G,tn)
Proof
  cheat
QED
