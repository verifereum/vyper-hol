(* Reuse the generic PHI provenance relation for every recursive encoder action. *)
Theory abiEncoderPhi
Ancestors
  abiDecoderPhi abiEncoderAppend abiEncoder compileEnv emitHelper context venomInst
  venomExecSemantics list pair

Definition abi_encoder_phi_def:
  abi_encoder_phi (action : 'a compiler) <=>
    !st. abi_decoder_phi st (SND (action st))
End

Theorem abi_encoder_phi_bind:
  abi_encoder_phi action /\ (!v. abi_encoder_phi (next v)) ==>
  abi_encoder_phi (comp_bind action next)
Proof
  simp_tac bool_ss [abi_encoder_phi_def] >> strip_tac >> gen_tac >>
  irule abi_decoder_phi_bind >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_phi_ignore_bind:
  abi_encoder_phi action /\ abi_encoder_phi next ==>
  abi_encoder_phi (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >> irule abi_encoder_phi_bind >> simp[]
QED

Theorem abi_encoder_phi_return:
  abi_encoder_phi (comp_return v)
Proof
  simp[abi_encoder_phi_def, abi_decoder_phi_return]
QED

Theorem abi_encoder_phi_prims:
  (!opc ops. opc <> PHI ==> abi_encoder_phi (emit_op opc ops)) /\
  (!opc ops. opc <> PHI ==> abi_encoder_phi (emit_void opc ops)) /\
  (!opc ops outs. opc <> PHI ==> abi_encoder_phi (emit_inst opc ops outs)) /\
  (!prefix. abi_encoder_phi (fresh_label prefix)) /\ (!lbl. abi_encoder_phi (new_block lbl))
Proof
  simp[abi_encoder_phi_def, abi_decoder_phi_emit_op, abi_decoder_phi_emit_void,
    abi_decoder_phi_emit_inst, abi_decoder_phi_fresh_label, abi_decoder_phi_new_block]
QED

fun encode_phi_tac extra g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
      (extra @ [abi_encoder_phi_return, abi_encoder_phi_prims, LET_THM])],
    first_x_assum (fn th => FIRST_PROVE [irule (SRULE[] th) >> asm_simp_tac (srw_ss()) []]),
    ho_match_mp_tac abi_encoder_phi_bind >> conj_tac
      >- encode_phi_tac extra >> rpt gen_tac >> encode_phi_tac extra,
    ho_match_mp_tac abi_encoder_phi_ignore_bind >> conj_tac >> encode_phi_tac extra,
    IF_CASES_TAC >> fs[] >> encode_phi_tac extra]) g;

Theorem abi_encoder_phi_alloc:
  abi_encoder_phi (compile_alloc_buffer n)
Proof
  rewrite_tac [compile_alloc_buffer_def] >> encode_phi_tac []
QED

Theorem abi_encoder_phi_static:
  abi_encoder_phi (compile_abi_encode_static dst src)
Proof
  rewrite_tac [compile_abi_encode_static_def] >> encode_phi_tac []
QED

Theorem abi_encoder_phi_static_info:
  !dst src ei. abi_encoder_phi (compile_abi_encode_static_info dst src ei)
Proof
  rpt gen_tac >> Cases_on `ei` >> rewrite_tac [compile_abi_encode_static_info_def] >>
  encode_phi_tac [abi_encoder_phi_static]
QED

Theorem abi_encoder_phi_static_loop:
  abi_encoder_phi (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rewrite_tac [compile_abi_encode_dyn_static_loop_def] >> simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  encode_phi_tac [abi_encoder_phi_alloc, abi_encoder_phi_static_info]
QED

Theorem abi_encoder_phi_mutual:
  (!dst src ei dyn off ptr. abi_encoder_phi (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. abi_encoder_phi (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr. abi_encoder_phi (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len. abi_encoder_phi (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >> ONCE_REWRITE_TAC [compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  TRY (drule_all abi_encoder_complex_append_bindings >> strip_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  encode_phi_tac [abi_encoder_phi_static, abi_encoder_phi_alloc, abi_encoder_phi_static_loop]
QED

Theorem abi_encoder_child_exit_phi:
  compile_abi_encode_child dst src ei dyn off dyn_ptr st = (out,st') ==>
  st.cs_blocks = st'.cs_blocks \/ phi_prefix_length st'.cs_current_insts = 0
Proof
  strip_tac >> `abi_decoder_phi st st'` by
    metis_tac[cj 1 abi_encoder_phi_mutual, abi_encoder_phi_def, SND] >>
  fs[abi_decoder_phi_def]
QED

Theorem abi_encoder_core_exit_phi:
  compile_abi_encode_to_buf dst src ei st = (out,st') ==>
  st.cs_blocks = st'.cs_blocks \/ phi_prefix_length st'.cs_current_insts = 0
Proof
  strip_tac >> `abi_decoder_phi st st'` by
    metis_tac[cj 2 abi_encoder_phi_mutual, abi_encoder_phi_def, SND] >>
  fs[abi_decoder_phi_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_PHI_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder PHI provenance not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderPhi");
