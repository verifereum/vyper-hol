(* Pure source invariants for the current child and the remaining compiler call. *)
Theory abiEncoderMembersSource
Ancestors
  abiEncoderMembersDefs abiEncoderMembersInput abiEncoderInput abiEncoderChildInputs
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract compileEnv
  valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_members_pre_cons:
  abi_encoder_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d output_size b cap s ==>
  has_type ty av /\ has_types tys avs /\
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_input ei ty av (sb+so) mem_sz s.vs_memory /\
  abi_encoder_members_pre infos tys avs st src dst sb (so+mem_sz) d output_size b cap s
Proof
  strip_tac >> qpat_x_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_members_input_cons >> strip_tac >>
  `has_types tys avs` by (imp_res_tac abi_encoder_input_typed >> fs[Once has_type_def]) >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  asm_simp_tac bool_ss [abi_encoder_members_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_members_child_buffer:
  abi_encoder_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d output_size b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ st.cs_next_var <= prepared.cs_next_var /\
  abi_decoder_operand_live prepared.cs_next_var elem_src /\
  eval_operand elem_src actual = SOME (n2w (sb+so)) ==>
  abi_encoder_buffer_pre ei ty av prepared elem_src dst (sb+so) mem_sz d output_size b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_members_input_cons >> strip_tac >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  `actual.vs_memory = initial.vs_memory /\ eval_operand dst actual = SOME (n2w d)`
    by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live prepared.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_buffer_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_MEMBERS_SOURCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder members source not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderMembersSource");
