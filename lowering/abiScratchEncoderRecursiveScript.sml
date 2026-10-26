(* Structural closure of the precise encoder for actual translated descriptors.
   TOP-LEVEL: abi_scratch_encoder_translation removes all child execution
   hypotheses; complete source memory and physical resources remain explicit. *)
Theory abiScratchEncoderRecursive
Ancestors
  abiScratchEncoderArray abiScratchEncoderComplex abiScratchEncoderLeaves abiScratchEncoderContract
  abiEncoderAdmissible abiEncoder exprLowering compileEnv list pair

Theorem abi_scratch_encoder_admissible_mutual:
  (!ei. abi_encoder_admissible ei ==> abi_scratch_encoder ei) /\
  (!infos. abi_encoder_members_admissible infos ==> EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos)
Proof
  ho_match_mp_tac abi_encoder_admissible_ind >>
  rw[abi_encoder_admissible_def, EVERY_DEF, abi_scratch_encoder_word,
    abi_scratch_encoder_copy, abi_scratch_encoder_bytes] >> gvs[] >>
  FIRST [irule abi_scratch_encoder_array >> asm_simp_tac (srw_ss()) [],
    irule abi_scratch_encoder_complex >> asm_simp_tac bool_ss []]
QED

Theorem abi_scratch_encoder_admissible:
  abi_encoder_admissible ei ==> abi_scratch_encoder ei
Proof
  simp[cj 1 abi_scratch_encoder_admissible_mutual]
QED

Theorem abi_scratch_encoder_translation:
  abi_scratch_encoder (type_to_abi_enc_info sf ce ty)
Proof
  irule abi_scratch_encoder_admissible >> simp[abi_encoder_translation_admissible]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ENCODER_RECURSIVE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI precise translated encoder not kernel closed: " ^ n)
  end) (DB.thms "abiScratchEncoderRecursive");
