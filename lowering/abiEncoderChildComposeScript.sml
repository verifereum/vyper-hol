(* Compose setup, recursive execution and parent-owned bookkeeping effects. *)
Theory abiEncoderChildCompose
Ancestors
  abiDecoderEffect abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderReentry
  abiDecoderContract abiDecoderLoop compileEnv venomState arithmetic

Theorem abi_encoder_child_compose:
  abi_decoder_address_frame next initial ready /\ fresh_vars_wrt limit_st ready /\
  abi_decoder_budget first last b cap initial /\
  abi_decoder_effect first last child_lo child_hi child_next limit_st child_d child_sz b cap ready encoded /\
  abi_decoder_effect first last lo hi suffix_next limit_st d sz b cap encoded actual /\
  lo <= child_lo /\ child_hi <= hi /\ next <= child_next /\ next <= suffix_next /\
  d <= child_d /\ child_d+child_sz <= d+sz /\
  abi_decode_sim ctx func initial ready /\ abi_decode_sim ctx func ready encoded /\
  abi_decode_sim ctx func encoded actual ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap initial actual /\
  abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap initial ready` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >> qexists_tac `next` >> simp[]) >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap ready encoded` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`child_d`, `child_hi`, `child_lo`, `child_next`, `child_sz`] >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap encoded actual` by
    (irule abi_decoder_effect_widen >> qexistsl_tac [`d`, `hi`, `lo`, `suffix_next`, `sz`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  conj_tac
  >- (irule abi_decoder_effect_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
      irule abi_decoder_effect_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []) >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CHILD_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder child composition not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderChildCompose");
