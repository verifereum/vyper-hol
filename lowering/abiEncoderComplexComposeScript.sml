(* Sequential recursive effects can grow their owned interval and local-variable frontier. *)
Theory abiEncoderComplexCompose
Ancestors
  abiDecoderEffect abiDecoderLoop abiDecoderContract compileEnv venomState arithmetic

Theorem abi_decoder_effect_sequence:
  abi_decoder_effect first last lo mid next limit_st d sz b cap initial ready /\
  abi_decoder_effect first last lo hi later limit_st d sz b cap ready actual /\
  mid <= hi /\ next <= later ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap initial ready` by
    (irule abi_decoder_effect_widen >> qexistsl_tac [`d`, `mid`, `lo`, `next`, `sz`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap ready actual` by
    (irule abi_decoder_effect_widen >> qexistsl_tac [`d`, `hi`, `lo`, `later`, `sz`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  irule abi_decoder_effect_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_complex_compose:
  abi_decoder_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
    limit_st d sz b cap initial ready /\
  abi_decoder_effect first last st.cs_next_id middle.cs_next_id prepared.cs_next_var
    limit_st d sz b cap ready encoded /\
  abi_decoder_effect first last st.cs_next_id end_st.cs_next_id middle.cs_next_var
    limit_st d sz b cap encoded actual /\
  prepared.cs_next_id <= middle.cs_next_id /\ middle.cs_next_id <= end_st.cs_next_id /\
  st.cs_next_var <= prepared.cs_next_var /\ prepared.cs_next_var <= middle.cs_next_var /\
  abi_decode_sim ctx func initial ready /\ abi_decode_sim ctx func ready encoded /\
  abi_decode_sim ctx func encoded actual ==>
  abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_effect first last st.cs_next_id middle.cs_next_id st.cs_next_var
    limit_st d sz b cap initial encoded` by
    (mp_tac (Q.INST [`ready` |-> `ready:venom_state`, `actual` |-> `encoded:venom_state`,
      `lo` |-> `st.cs_next_id`, `hi` |-> `middle.cs_next_id`, `next` |-> `st.cs_next_var`,
      `later` |-> `prepared.cs_next_var`, `mid` |-> `prepared.cs_next_id`]
      abi_decoder_effect_sequence) >> asm_simp_tac bool_ss []) >>
  conj_tac
  >- (mp_tac (Q.INST [`ready` |-> `encoded:venom_state`, `lo` |-> `st.cs_next_id`,
        `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`, `later` |-> `middle.cs_next_var`,
        `mid` |-> `middle.cs_next_id`] abi_decoder_effect_sequence) >>
      impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> asm_simp_tac bool_ss []) >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_COMPLEX_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder complex composition not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderComplexCompose");
