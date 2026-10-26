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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CORRECT_LEAVES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder leaf correctness not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCorrectLeaves");
