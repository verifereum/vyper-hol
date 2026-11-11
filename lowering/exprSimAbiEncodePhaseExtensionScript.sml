Theory exprSimAbiEncodePhaseExtension
Ancestors
  exprSimAbiEncodeSetupExtension exprSimAbiEncodeFinishExtension
  exprSimAbiEncodeObservationExtension exprSimAbiEncodeExtension
  exprSimAbiEncodeStagedObserver exprSimAbiEncodeExecFrame
  abiEncoderWindowContract abiEncoderExtendSim abiDecoderVarExtend varsExt venomState

Theorem abi_encode_phases_extend:
  abi_encoder_extend_sim ctx obs initial prepared /\
  window_strong_result ctx obs body_st body_end out at av d prepared encoded /\
  abi_encoder_extend_sim ctx obs encoded actual ==>
  abi_encoder_extend_sim ctx obs initial actual
Proof
  strip_tac >>
  `abi_encoder_extend_sim ctx obs prepared encoded` by
    gvs[window_strong_result_def] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `prepared` >> simp[] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `encoded` >> simp[]
QED

(* The initial observation parameter is deliberately unchanged. Callers must
   establish it relative to their original state, not just the cleaned input. *)
Theorem abi_encode_lift_clean_observation:
  abi_encoder_extend_sim ctx obs (drop_fresh st s) u /\
  abi_encode_staged_observation c f ce cx vs origin out mid outsz p at av initial u /\
  abi_encode_exec_frame obs initial u ==>
  ?v. abi_decode_sim ctx obs s v /\ abi_decoder_vars_extend s.vs_vars u v /\
    abi_encode_staged_observation c f ce cx vs origin out mid outsz p at av initial v /\
    abi_encode_exec_frame obs initial v
Proof
  strip_tac >> drule abi_encode_extend_clean_input >> strip_tac >>
  qexists_tac `v` >> simp[] >> conj_tac
  >- (irule abi_encode_staged_observation_extend >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >>
  irule abi_encode_exec_frame_extend >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any)
QED
