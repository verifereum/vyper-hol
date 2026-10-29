(* One structural closure of the shared encoder execution contract. *)
Theory abiEncoderSharedRecursive
Ancestors
  abiEncoderSharedLeaves abiEncoderSharedArray abiEncoderSharedComplex
  abiEncoderAdmissible abiEncoder exprLowering compileEnv list pair

Theorem abi_encoder_shared_admissible_mutual:
  (!ei. abi_encoder_admissible ei ==> abi_encoder_shared ei) /\
  (!infos. abi_encoder_members_admissible infos ==>
    EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos)
Proof
  ho_match_mp_tac abi_encoder_admissible_ind >>
  rw[abi_encoder_admissible_def, EVERY_DEF, abi_encoder_shared_word,
    abi_encoder_shared_copy, abi_encoder_shared_bytes] >> gvs[]
  >- (irule abi_encoder_shared_array >> simp[])
  >- (irule abi_encoder_shared_array >> simp[]) >>
  irule abi_encoder_shared_complex >> asm_rewrite_tac []
QED

Theorem abi_encoder_shared_admissible:
  abi_encoder_admissible ei ==> abi_encoder_shared ei
Proof
  simp[cj 1 abi_encoder_shared_admissible_mutual]
QED

Theorem abi_encoder_shared_translation:
  abi_encoder_shared (type_to_abi_enc_info sf ce ty)
Proof
  irule abi_encoder_shared_admissible >> simp[abi_encoder_translation_admissible]
QED
