(* Every complex constructor has the precise contract once its children do.
   TOP-LEVEL: abi_scratch_encoder_complex selects the actual static/dynamic
   branch without a whole numeric scratch-arena exclusion. *)
Theory abiScratchEncoderComplex
Ancestors
  abiScratchComplex abiScratchEncoderContract abiEncoder list

Theorem abi_scratch_encoder_complex:
  EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos ==>
  abi_scratch_encoder (AbiComplex infos)
Proof
  strip_tac >> Cases_on `EXISTS (\(_,_,_,dyn). dyn) infos`
  >- (irule abi_scratch_encoder_complex_dynamic >> asm_simp_tac bool_ss []) >>
  irule abi_scratch_encoder_complex_static >> asm_simp_tac bool_ss []
QED
