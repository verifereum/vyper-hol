(* Reusable composition of an address-only prefix and an owned encoder effect. *)
Theory abiEncoderAfterAddress
Ancestors
  abiDecoderEffect abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderLoop
  abiDecoderContract compileEnv venomState arithmetic

Theorem abi_encoder_after_address:
  abi_decoder_address_frame next initial ready /\ fresh_vars_wrt limit_st ready /\
  abi_sites_decoder_budget sites first last b cap initial /\
  abi_sites_decoder_effect sites first last child_lo child_hi child_next limit_st
    child_d child_sz b cap ready actual /\
  lo <= child_lo /\ child_hi <= hi /\ next <= child_next /\
  d <= child_d /\ child_d+child_sz <= d+sz /\
  abi_decode_sim ctx func initial ready /\ abi_decode_sim ctx func ready actual ==>
  abi_sites_decoder_effect sites first last lo hi next limit_st d sz b cap initial actual /\
  abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_sites_decoder_effect sites first last lo hi next limit_st d sz b cap initial ready` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >> qexists_tac `next` >> simp[]) >>
  `abi_sites_decoder_effect sites first last lo hi next limit_st d sz b cap ready actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`child_d`, `child_hi`, `child_lo`, `child_next`, `child_sz`] >>
     asm_simp_tac bool_ss []) >>
  conj_tac
  >- (irule abi_decoder_effect_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED
