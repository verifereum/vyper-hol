(* Every complex descriptor is correct once its recursive child descriptors are correct. *)
Theory abiEncoderCorrectComplex
Ancestors
  abiEncoderComplexStatic abiEncoderComplexDynamic abiEncoderCorrect abiEncoder list

Theorem abi_encoder_correct_complex:
  EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos ==>
  abi_encoder_correct (AbiComplex infos)
Proof
  strip_tac >> Cases_on `EXISTS (\(_,_,_,dyn). dyn) infos`
  >- (irule abi_encoder_correct_complex_dynamic >> asm_simp_tac bool_ss []) >>
  irule abi_encoder_correct_complex_static >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CORRECT_COMPLEX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder complex correctness not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderCorrectComplex");
