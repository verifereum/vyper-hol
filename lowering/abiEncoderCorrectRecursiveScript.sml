(* Structural closure removes the child-correctness premises for actual translated descriptors. *)
Theory abiEncoderCorrectRecursive
Ancestors
  abiEncoderSharedRecursive abiEncoderEnvelopeAdapter
  abiEncoderAdmissible abiEncoder exprLowering compileEnv list pair

Theorem abi_encoder_correct_admissible_mutual:
  (!ei. abi_encoder_admissible ei ==> abi_encoder_correct ei) /\
  (!infos. abi_encoder_members_admissible infos ==> EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos)
Proof
  conj_tac
  >- (metis_tac[abi_encoder_shared_admissible, abi_encoder_shared_correct]) >>
  rpt strip_tac >>
  drule (cj 2 abi_encoder_shared_admissible_mutual) >>
  simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >>
  metis_tac[abi_encoder_shared_correct]
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
