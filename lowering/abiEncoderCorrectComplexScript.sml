(* Every complex descriptor is correct once its recursive child descriptors are correct. *)
Theory abiEncoderCorrectComplex
Ancestors
  abiEncoderComplexDynamic abiEncoderComplexDynamic abiEncoderCorrect abiEncoder list

Theorem abi_encoder_correct_complex:
  EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos ==>
  abi_encoder_correct (AbiComplex infos)
Proof
  strip_tac >> Cases_on `EXISTS (\(_,_,_,dyn). dyn) infos`
  >- (irule abi_encoder_correct_complex_dynamic >> asm_simp_tac bool_ss []) >>
  irule abi_encoder_correct_complex_static >> asm_simp_tac bool_ss []
QED
