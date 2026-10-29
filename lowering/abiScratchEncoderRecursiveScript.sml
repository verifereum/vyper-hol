(* Structural closure of the precise encoder for actual translated descriptors.
   TOP-LEVEL: abi_scratch_encoder_translation removes all child execution
   hypotheses; complete source memory and physical resources remain explicit. *)
Theory abiScratchEncoderRecursive
Ancestors
  abiEncoderSharedRecursive abiEncoderSharedContract
  abiEncoderAdmissible abiEncoder exprLowering compileEnv list pair

Theorem abi_scratch_encoder_admissible_mutual:
  (!ei. abi_encoder_admissible ei ==> abi_scratch_encoder ei) /\
  (!infos. abi_encoder_members_admissible infos ==> EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos)
Proof
  conj_tac
  >- (metis_tac[abi_encoder_shared_admissible, abi_encoder_shared_scratch]) >>
  rpt strip_tac >>
  drule (cj 2 abi_encoder_shared_admissible_mutual) >>
  simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >>
  metis_tac[abi_encoder_shared_scratch]
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
