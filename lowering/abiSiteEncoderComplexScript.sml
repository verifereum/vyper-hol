(* Finite-site constructor assembly around the single member interpreter. *)
Theory abiSiteEncoderComplex
Ancestors
  abiScratchMembersInterpret abiScratchMembersIndex abiScratchMembers
  abiEncoderChildCapability abiEncoderChildContext abiSiteEncoderContract abiEncoderMemberSpine
  abiSiteEncoderBoundary abiEncoderComplexCode abiEncoderComplexDynamic
  abiEncoderComplexPrefix abiEncoderMembersInput abiEncoderTuple
  abiScratchAddress abiScratchEffect abiDecoderLoop abiDecoderContract
  compileEnv valueEncoding contractABI venomState list arithmetic

Theorem abi_site_members_run:
  EVERY (\(ei,_,_,_). abi_site_encoder ei) infos /\
  compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_site_members_inv infos tys avs pre pvs active dyn_ptr site slot A lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_decoder_emitted_sites st.cs_next_id end_st.cs_next_id st end_st SUBSET A /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. abi_site_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot A lo
      end_st limit_st src dst sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
    abi_site_encoder_effect A lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\ abi_decode_sim ctx func initial t
Proof
  strip_tac >>
  `EVERY (\(ei,_,_,_). abi_encoder_child_capability A
    (\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A) ei) infos` by
    (irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
     simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
     metis_tac[abi_encoder_child_capability_site]) >>
  drule_all (Q.INST [`hi` |-> `end_st.cs_next_id`] abi_site_members_index_initial) >>
  disch_then (qspecl_then [`func`,`end_st`,`ctx`] assume_tac) >>
  `abi_encoder_spine_code func limit_st end_st.cs_next_id (dst,src,dyn_ptr)
    infos (st,so,ho) (out,end_st)` by simp[abi_encoder_spine_code_def] >>
  drule_all (SRULE [abi_encoder_hereditary_guard_sites] (Q.INST
    [`guard` |-> `\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A`]
    abi_site_members_generate)) >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac []
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if not (null (Thm.hyp th)) orelse not (null axs) orelse
       List.exists (fn s => s <> "DISK_THM") ors
    then raise Fail ("Finite-site complex dependency: " ^ name) else ()
  end) (DB.thms "abiSiteEncoderComplex");
