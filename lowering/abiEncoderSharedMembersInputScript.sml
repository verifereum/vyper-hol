(* Open remaining-member windows with physical scratch separation. *)
Theory abiEncoderSharedMembersInput
Ancestors
  abiEncoderSharedContract abiEncoderOpenInput abiEncoderOpenInputFrame abiEncoderInput abiEncoderZeroFrame
  abiEncoderMembersDefs abiDecoderReentry abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint
  abiScratchEncoderContract abiScratchEffect abiScratchSubset abiScratchFootprint abiDecoderFrame
  abiEncoderArrayFrame compileEnv valueEncoding venomState venomMemDefs list arithmetic words pred_set

Definition abi_encoder_shared_members_pre_def:
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap s <=>
    abi_encoder_open_input (AbiComplex infos) (Tuple tys) (ListV avs)
      (sb+so) (abi_encoder_member_span infos) s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    sb+so+abi_encoder_member_span infos < dimword (:256) /\ d+sz < dimword (:256) /\
    regions_disjoint (sb+so,abi_encoder_member_span infos) (d,sz) /\
    abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
    abi_footprint_disjoint d sz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
End

Theorem abi_encoder_shared_members_pre_mono:
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_shared_members_pre infos tys avs prepared src dst sb so d sz first last b cap s
Proof
  simp_tac bool_ss [abi_encoder_shared_members_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_encoder_shared_members_pre_address:
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_shared_members_pre infos tys avs prepared src dst sb so d sz first last b cap actual
Proof
  simp_tac bool_ss [abi_encoder_shared_members_pre_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial` by
    simp[abi_decoder_child_scratch_def] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_encoder_shared_members_pre_shape:
  abi_encoder_shared_members_pre ((ei,az,mz,dyn)::infos) tys avs
    st src dst sb so d sz first last b cap s ==>
  ?ty ts av vs. tys = ty::ts /\ avs = av::vs
Proof
  simp_tac bool_ss [abi_encoder_shared_members_pre_def] >> strip_tac >>
  `LENGTH ((ei,az,mz,dyn)::infos) = LENGTH tys /\ LENGTH tys = LENGTH avs` by
    (qpat_assum `abi_encoder_open_input _ _ _ _ _ _`
      (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
     simp_tac (srw_ss()) [abi_encoder_open_complex_iff, abi_encoder_tuple_type_def] >>
     rpt strip_tac >> gvs[]) >>
  Cases_on `tys` >- gvs[] >> Cases_on `avs` >- gvs[] >> simp[]
QED

Theorem abi_encoder_shared_members_pre_empty:
  abi_encoder_shared_members_pre [] tys avs st src dst sb so d sz first last b cap s ==>
  tys = [] /\ avs = []
Proof
  simp[abi_encoder_shared_members_pre_def, abi_encoder_open_complex_nil]
QED
Theorem abi_encoder_shared_open_input_frame:
  abi_encoder_open_input ei at av sb cap s.vs_memory /\
  abi_decode_footprint_frame fp s t /\ abi_footprint_disjoint sb cap fp ==>
  abi_encoder_open_input ei at av sb cap t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at sb cap s.vs_memory = mem_bytes_at sb cap t.vs_memory` by
    (drule_all abi_decode_footprint_frame_slice >> simp[EQ_SYM_EQ]) >>
  drule_all abi_encoder_open_input_mem_agree >> simp[]
QED

Theorem abi_encoder_shared_members_pre_effect:
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap initial /\
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
  first <= lo /\ hi <= last ==>
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_pre_def]) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (imp_res_tac abi_scratch_effect_operand >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `mem_bytes_at (sb+so) (abi_encoder_member_span infos) initial.vs_memory =
   mem_bytes_at (sb+so) (abi_encoder_member_span infos) actual.vs_memory` by
    (drule_all abi_encoder_footprint_frame_zero_slice >> simp[EQ_SYM_EQ]) >>
  `abi_encoder_open_input (AbiComplex infos) (Tuple tys) (ListV avs) (sb+so)
    (abi_encoder_member_span infos) actual.vs_memory` by
    (drule_all abi_encoder_open_input_mem_agree >> simp[]) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
   abi_footprint_disjoint d sz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (conj_tac >> irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_shared_members_pre_def]
QED

Theorem abi_encoder_shared_members_pre_cons:
  abi_encoder_shared_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d sz first last b cap s ==>
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_open_input ei ty av (sb+so) mem_sz s.vs_memory /\
  abi_encoder_shared_members_pre infos tys avs st src dst sb (so+mem_sz) d sz first last b cap s
Proof
  strip_tac >> qpat_x_assum `abi_encoder_shared_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_pre_def]) >>
  drule abi_encoder_open_complex_cons >> strip_tac >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  `abi_footprint_disjoint (sb+(so+mem_sz)) (abi_encoder_member_span infos)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`sb+so`, `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `regions_disjoint (sb+(so+mem_sz),abi_encoder_member_span infos) (d,sz)` by
    (gvs[abi_encoder_zero_aware_separation] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_encoder_shared_members_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_shared_members_child_buffer:
  abi_encoder_shared_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d sz first last b cap s /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  eval_operand elem_src s = SOME (n2w (sb+so)) /\ LENGTH (enc ty av) <= sz ==>
  abi_encoder_shared_input (ei,ty,av) (st,elem_src,dst) (sb+so,mem_sz) (d,sz) (first,last,b,cap) s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_shared_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_pre_def]) >>
  drule abi_encoder_open_complex_cons >> strip_tac >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  `abi_footprint_disjoint (sb+so) mem_sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`sb+so`, `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `regions_disjoint (sb+so,mem_sz) (d,sz)` by
    (gvs[abi_encoder_zero_aware_separation] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_encoder_shared_input_def] >> decide_tac
QED


val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared members input admission, axiom or hypothesis"
  end) [abi_encoder_shared_members_pre_mono, abi_encoder_shared_members_pre_address,
    abi_encoder_shared_members_pre_shape, abi_encoder_shared_members_pre_empty,
    abi_encoder_shared_open_input_frame, abi_encoder_shared_members_pre_effect,
    abi_encoder_shared_members_pre_cons, abi_encoder_shared_members_child_buffer];
