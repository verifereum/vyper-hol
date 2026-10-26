(* Remaining tuple members retain complete source data and physical scratch
   separation. Source offsets refer to the original, live source operand.
   TOP-LEVEL: abi_scratch_members_pre and its state transport lemmas. *)
Theory abiScratchMembersPre
Ancestors
  abiScratchEncoderContract abiScratchEffectProtected abiScratchFootprint abiScratchSubset
  abiEncoderInputFrame abiEncoderInput abiEncoderMembersInput
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  compileEnv valueEncoding venomState pred_set words list arithmetic

Definition abi_scratch_members_pre_def:
  abi_scratch_members_pre infos tys avs st src dst sb so d output_size first last b cap s <=>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
      (sb+so) (abi_encoder_member_span infos) s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    sb+so+abi_encoder_member_span infos < dimword (:256) /\
    d+output_size < dimword (:256) /\
    (sb+so+abi_encoder_member_span infos <= d \/ d+output_size <= sb+so) /\
    abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
End

Theorem abi_scratch_members_pre_mono:
  abi_scratch_members_pre infos tys avs st src dst sb so d sz first last b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_members_pre infos tys avs prepared src dst sb so d sz first last b cap s
Proof
  simp_tac bool_ss [abi_scratch_members_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_scratch_members_pre_address:
  abi_scratch_members_pre infos tys avs st src dst sb so d sz first last b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_members_pre infos tys avs prepared src dst sb so d sz first last b cap actual
Proof
  simp_tac bool_ss [abi_scratch_members_pre_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial` by
    simp[abi_decoder_child_scratch_def] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_scratch_members_pre_effect:
  abi_scratch_members_pre infos tys avs st src dst sb so d sz first last b cap initial /\
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
  first <= lo /\ hi <= last ==>
  abi_scratch_members_pre infos tys avs st src dst sb so d sz first last b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)` by
    simp[abi_scratch_disjoint_cons] >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (imp_res_tac abi_scratch_effect_operand >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) (sb+so)
    (abi_encoder_member_span infos) actual.vs_memory` by
    (drule_all abi_encoder_input_frame >> simp[]) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
   abi_footprint_disjoint d sz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (conj_tac >> irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_members_pre_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_MEMBERS_PRE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch member input not kernel closed: " ^ n)
  end) (DB.thms "abiScratchMembersPre");
