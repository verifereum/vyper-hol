(* Precise child write windows retain earlier tuple heads and tails. *)
Theory abiEncoderChildFrames
Ancestors
  abiDecoderDynamicLoopSetup abiDecoderFrame abiDecoderReentry abiDecoderContract
  compileEnv venomState list arithmetic

Theorem abi_encoder_frame_after_address:
  abi_decoder_address_frame next initial ready /\ abi_decode_footprint_frame fp ready actual ==>
  abi_decode_footprint_frame fp initial actual
Proof
  simp_tac bool_ss [abi_decoder_address_frame_def, abi_decode_footprint_frame_def] >>
  strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_frame_extra_window:
  abi_decode_footprint_frame fp initial actual ==>
  abi_decode_footprint_frame (window::fp) initial actual
Proof
  strip_tac >> irule abi_decode_footprint_frame_weaken >> qexists_tac `fp` >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >> qexistsl_tac [`d`, `sz`] >> simp[]
QED

Theorem abi_encoder_dynamic_child_frame:
  abi_decoder_address_frame next initial ready /\
  abi_decode_footprint_frame [(q,len);(b,cap)] ready encoded /\
  abi_decode_footprint_frame [(h,32);(slot,32)] encoded actual /\
  b <= slot /\ slot+32 <= b+cap ==>
  abi_decode_footprint_frame [(h,32);(q,len);(b,cap)] initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_footprint_frame [(h,32);(q,len);(b,cap)] ready encoded` by
    (irule abi_encoder_frame_extra_window >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(h,32);(q,len);(b,cap)] encoded actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(h,32);(slot,32)]` >>
     asm_simp_tac bool_ss [] >> simp[] >> rpt gen_tac >> strip_tac >|
     [qexistsl_tac [`h`, `32`] >> simp[], qexistsl_tac [`b`, `cap`] >> simp[]]) >>
  irule abi_encoder_frame_after_address >> qexistsl_tac [`next`, `ready`] >>
  asm_simp_tac bool_ss [] >> irule abi_decode_footprint_frame_trans >>
  qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED
