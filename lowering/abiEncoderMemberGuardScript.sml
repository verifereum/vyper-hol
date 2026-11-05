(* Compiler-only guard restrictions for the shared member interpreter. *)
Theory abiEncoderMemberGuard
Ancestors
  abiEncoderChildContext abiEncoderMemberSpine abiDecoderSiteMembership
  abiEncoderChildCode abiEncoderCounters abiEncoderAddressReach abiEncoderAppend
  emitHelperProps compileEnv
  pred_set list arithmetic


Theorem abi_encoder_members_cons_guard:
  abi_encoder_hereditary_guard G /\
  compile_abi_encode_complex_elems dst src ((ei,az,mz,dyn)::infos) so ho dp st = (out0,end0) /\
  G st end0 /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp)
    ((ei,az,mz,dyn)::infos) (st,so,ho) (out,en) /\
  abi_encoder_spine_cons_layout func limit_st hi (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) ==>
  out = out0 /\ en = end0 /\ G p ce /\ G ce end0 /\
  compile_abi_encode_complex_elems dst src infos (so+mz) (ho+az) dp ce = (out0,end0)
Proof
  simp_tac bool_ss [abi_encoder_spine_code_def, abi_encoder_spine_cons_layout_def] >>
  strip_tac >> gvs[] >>
  `cs_extends st ce` by
    (irule cs_extends_trans >> qexists_tac `p` >> asm_rewrite_tac []) >>
  `cs_extends en en` by simp[cs_extends_refl] >>
  qpat_x_assum `abi_encoder_hereditary_guard G` mp_tac >>
  simp_tac bool_ss [abi_encoder_hereditary_guard_def] >>
  disch_tac >> conj_tac
  >- (first_x_assum irule >> asm_rewrite_tac [] >> qexistsl_tac [`st`,`en`] >> asm_rewrite_tac [] >> decide_tac) >>
  first_x_assum irule >> asm_rewrite_tac [] >> qexistsl_tac [`st`,`en`] >> asm_rewrite_tac [] >> decide_tac
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Encoder member guard dependency" else ()
  end) [abi_encoder_hereditary_guard_interval, abi_encoder_hereditary_guard_sites,
         abi_encoder_members_cons_guard, abi_encoder_static_child_guard,
         abi_encoder_dynamic_child_guard];
