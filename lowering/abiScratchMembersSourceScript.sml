(* Select the next member and advance the remaining physical source window.
   TOP-LEVEL: abi_scratch_members_pre_cons and abi_scratch_members_child_buffer.
   No numeric exclusion of the entire scratch arena is required. *)
Theory abiScratchMembersSource
Ancestors
  abiScratchMembersPre abiScratchEncoderContract abiEncoderMembersInput abiEncoderInput
  abiEncoderArrayFrame abiDecoderFrame abiDecoderReentry compileEnv
  valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_members_pre_cons:
  abi_scratch_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d output_size first last b cap s ==>
  has_type ty av /\ has_types tys avs /\
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_input ei ty av (sb+so) mem_sz s.vs_memory /\
  abi_scratch_members_pre infos tys avs st src dst sb (so+mem_sz) d output_size first last b cap s
Proof
  strip_tac >> qpat_x_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_members_input_cons >> strip_tac >>
  `has_types tys avs` by (imp_res_tac abi_encoder_input_typed >> fs[Once has_type_def]) >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  `abi_footprint_disjoint (sb+(so+mem_sz)) (abi_encoder_member_span infos)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`sb+so`, `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_scratch_members_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_scratch_members_child_buffer:
  abi_scratch_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d output_size first last b cap s /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  eval_operand elem_src s = SOME (n2w (sb+so)) /\ LENGTH (enc ty av) <= output_size ==>
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_members_input_cons >> strip_tac >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  `abi_footprint_disjoint (sb+so) mem_sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`sb+so`, `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_scratch_input_def] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_MEMBERS_SOURCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch member selection not kernel closed: " ^ n)
  end) (DB.thms "abiScratchMembersSource");
