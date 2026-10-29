(* Primitive, Bytes, String and flag cases of the recursive correctness theorem. *)
Theory abiDecoderCorrectLeaves
Ancestors
  abiDecoderCorrect abiDecoderCorrectWord abiDecoderCorrectBytestring
  exprLowering compileEnv vyperValue vyperAST

Theorem abi_decoder_correct_base:
  abi_decoder_correct ce env sf (BaseT bt) (BaseTV bt)
Proof
  `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
   (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
    (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def]) >>
  FIRST [drule_all abi_decoder_correct_word >> simp[],
    drule_all abi_decoder_correct_bytestring >> simp[]]
QED

Theorem abi_decoder_correct_flag:
  abi_decoder_correct ce env sf (FlagT nsid) (FlagTV n)
Proof
  irule abi_decoder_correct_word >> simp[Once type_to_abi_dec_info_def]
QED
