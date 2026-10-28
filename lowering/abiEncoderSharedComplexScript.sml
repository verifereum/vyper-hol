(* Complex assembly around the single shared member execution spine. *)
Theory abiEncoderSharedComplex
Ancestors
  abiEncoderSharedMembersCorrect abiEncoderSharedMembersInput abiEncoderSharedMembersIndex
  abiEncoderSharedArrayPrepare abiEncoderSharedContract abiEncoderComplexLayout
  abiEncoderComplexPrefix abiEncoderOpenInput abiEncoderInput abiEncoderMembersDefs
  abiScratchEffect abiScratchEncoderContract abiEncoderRegisteredEffect abiEncoderExtendSim abiDecoderContract
  abiDecodeRanges abiDecoderReentry compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_shared_complex_head_length:
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap s ==>
  SUM (MAP (\(_,asz,_,_). asz) infos) = head_lengths tys 0
Proof
  simp_tac bool_ss [abi_encoder_shared_members_pre_def] >> strip_tac >>
  qpat_x_assum `abi_encoder_open_input _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_open_complex_iff]) >>
  gvs[abi_encoder_tuple_type_def] >> rename1 `head_lengths tys 0` >>
  `MAP (\(_,asz,_,_). asz) infos = MAP abi_member_head_size tys` by
    (irule (cj 1 abi_encoder_members_metadata) >> asm_simp_tac bool_ss [] >>
     rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  simp[head_lengths_acc]
QED

Theorem abi_encoder_shared_complex_prepare:
  abi_encode_complex_prefix infos st = (dp,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_shared_input (AbiComplex infos,at,ListV avs) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\ abi_encoder_tuple_type at tys /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  prepared.cs_next_id <= last /\ prepared.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_shared_members_inv infos tys avs [] [] T dp st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial ready /\
    abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id prepared.cs_next_id)
      [(d,output_size)] initial ready /\
    (alloca_inv initial ==> alloca_inv ready) /\ abi_encoder_extend_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_cursor_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready` (qx_choose_then `slot` strip_assume_tac))) >>
  drule_all abi_encoder_shared_members_root_pre >> strip_tac >>
  drule abi_encoder_shared_complex_head_length >> disch_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    fs[abi_scratch_effect_def] >>
  `abi_encoder_shared_members_inv infos tys avs [] [] T dp st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready` by
    (irule abi_encoder_shared_members_initial_inv >> fs[]) >>
  qexistsl_tac [`ready`,`slot`] >> asm_simp_tac bool_ss []
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared complex admission, axiom or hypothesis"
  end) [abi_encoder_shared_complex_head_length,abi_encoder_shared_complex_prepare];
