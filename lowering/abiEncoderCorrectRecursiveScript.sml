(* Structural closure removes the child-correctness premises for actual translated descriptors. *)
Theory abiEncoderCorrectRecursive
Ancestors
  abiEncoderCorrectArray abiEncoderCorrectComplex abiEncoderCorrectLeaves abiEncoderCorrect
  abiEncoderAdmissible abiEncoder exprLowering compileEnv list pair

Theorem abi_encoder_correct_admissible_mutual:
  (!ei. abi_encoder_admissible ei ==> abi_encoder_correct ei) /\
  (!infos. abi_encoder_members_admissible infos ==> EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos)
Proof
  ho_match_mp_tac abi_encoder_admissible_ind >>
  rw[abi_encoder_admissible_def, EVERY_DEF, abi_encoder_correct_word,
    abi_encoder_correct_copy, abi_encoder_correct_bytes] >> gvs[] >>
  FIRST [irule abi_encoder_correct_array >> asm_simp_tac (srw_ss()) [],
    irule abi_encoder_correct_complex >> asm_simp_tac bool_ss []]
QED

Theorem abi_encoder_correct_admissible:
  abi_encoder_admissible ei ==> abi_encoder_correct ei
Proof
  simp[cj 1 abi_encoder_correct_admissible_mutual]
QED

Theorem abi_encoder_correct_translation:
  abi_encoder_correct (type_to_abi_enc_info sf ce ty)
Proof
  irule abi_encoder_correct_admissible >> simp[abi_encoder_translation_admissible]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CORRECT_RECURSIVE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI recursive encoder correctness not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderCorrectRecursive");
