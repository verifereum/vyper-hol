(* Late source-fragment adapter; keep the registered-effect core independent of ABIProps. *)
Theory abiEncoderRegisteredFrame
Ancestors
  abiEncoderRegisteredEffect abiEncoderProps

Theorem abi_encoder_registered_effect_frame:
  abi_encoder_registered_effect (frag_ids st st') outs s0 s /\
  enc_scratch (frag_ids st st') lo top s /\
  (!x w. not_fresh_at st x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) ==>
  enc_frame st st' lo top outs s0 s
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def, enc_frame_def] >>
  metis_tac[]
QED
