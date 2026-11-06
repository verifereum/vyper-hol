(* Open remaining-member windows with physical scratch separation. *)
Theory abiEncoderSharedMembersInput
Ancestors
  abiEncoderSharedContract abiEncoderWindow abiEncoderOpenInput abiEncoderOpenInputFrame abiEncoderInput abiEncoderZeroFrame
  abiEncoderMembersDefs abiDecoderReentry abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint
  abiScratchEncoderContract abiScratchEffect abiScratchSubset abiScratchFootprint abiDecoderFrame
  abiEncoderArrayFrame compileEnv valueEncoding venomState venomMemDefs list arithmetic words pred_set

Definition abi_sites_encoder_shared_members_pre_def:
  abi_sites_encoder_shared_members_pre sites infos tys avs st src dst sb so d sz first last b cap s <=>
    (?rc. abi_encoder_window_input (AbiComplex infos) (Tuple tys) (ListV avs)
            (sb+so) (rc-so) s.vs_memory /\
          (infos <> [] ==> so <= rc) /\ sb+rc < dimword (:256) /\
          regions_disjoint (sb,rc) (d,sz) /\
          abi_footprint_disjoint sb rc (abi_decoder_child_scratch (abi_sites_decoder_ids sites first last) b cap s)) /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    d+sz < dimword (:256) /\
    abi_footprint_disjoint d sz
      (abi_decoder_child_scratch (abi_sites_decoder_ids sites first last) b cap s)
End

Overload abi_encoder_shared_members_pre = “abi_sites_encoder_shared_members_pre UNIV”

Theorem abi_encoder_shared_members_pre_def:
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap s <=>
    (?rc. abi_encoder_window_input (AbiComplex infos) (Tuple tys) (ListV avs)
            (sb+so) (rc-so) s.vs_memory /\
          (infos <> [] ==> so <= rc) /\ sb+rc < dimword (:256) /\
          regions_disjoint (sb,rc) (d,sz) /\
          abi_footprint_disjoint sb rc (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)) /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    d+sz < dimword (:256) /\
    abi_footprint_disjoint d sz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
Proof
  rewrite_tac[abi_sites_encoder_shared_members_pre_def]
QED

Theorem abi_encoder_shared_members_pre_mono:
  abi_sites_encoder_shared_members_pre sites infos tys avs st src dst sb so d sz first last b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_sites_encoder_shared_members_pre sites infos tys avs prepared src dst sb so d sz first last b cap s
Proof
  simp_tac bool_ss [abi_sites_encoder_shared_members_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_encoder_shared_members_pre_address:
  abi_sites_encoder_shared_members_pre sites infos tys avs st src dst sb so d sz first last b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_sites_encoder_shared_members_pre sites infos tys avs prepared src dst sb so d sz first last b cap actual
Proof
  simp_tac bool_ss [abi_sites_encoder_shared_members_pre_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_child_scratch (abi_sites_decoder_ids sites first last) b cap actual =
    abi_decoder_child_scratch (abi_sites_decoder_ids sites first last) b cap initial` by
    simp[abi_decoder_child_scratch_def] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_encoder_shared_members_pre_shape:
  abi_sites_encoder_shared_members_pre sites ((ei,az,mz,dyn)::infos) tys avs
    st src dst sb so d sz first last b cap s ==>
  ?ty ts av vs. tys = ty::ts /\ avs = av::vs
Proof
  simp_tac bool_ss [abi_sites_encoder_shared_members_pre_def] >> strip_tac >>
  `LENGTH ((ei,az,mz,dyn)::infos) = LENGTH tys /\ LENGTH tys = LENGTH avs` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _`
      (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
     simp_tac (srw_ss()) [abi_encoder_window_complex_iff, abi_encoder_tuple_type_def] >>
     rpt strip_tac >> gvs[]) >>
  Cases_on `tys` >- gvs[] >> Cases_on `avs` >- gvs[] >> simp[]
QED

Theorem abi_encoder_shared_members_pre_empty:
  abi_sites_encoder_shared_members_pre sites [] tys avs st src dst sb so d sz first last b cap s ==>
  tys = [] /\ avs = []
Proof
  simp_tac bool_ss [abi_sites_encoder_shared_members_pre_def] >> strip_tac >>
  gvs[abi_encoder_window_complex_nil]
QED
Theorem abi_encoder_shared_members_pre_effect:
  abi_sites_encoder_shared_members_pre sites infos tys avs st src dst sb so d sz first last b cap initial /\
  abi_sites_scratch_effect sites first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
  first <= lo /\ hi <= last ==>
  abi_sites_encoder_shared_members_pre sites infos tys avs st src dst sb so d sz first last b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_sites_encoder_shared_members_pre sites _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_sites_encoder_shared_members_pre_def]) >>
  qpat_x_assum `?rc. _` strip_assume_tac >>
  `abi_sites_decoder_ids sites lo hi SUBSET abi_sites_decoder_ids sites first last` by
    (simp[SUBSET_DEF, abi_sites_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint sb rc
    (abi_decoder_child_scratch (abi_sites_decoder_ids sites lo hi) b cap initial)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_sites_decoder_ids sites first last` >> simp[]) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (imp_res_tac abi_scratch_effect_operand >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_sites_scratch_effect sites _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_sites_scratch_effect_def]) >>
  `mem_bytes_at sb rc initial.vs_memory = mem_bytes_at sb rc actual.vs_memory` by
    (drule_all abi_encoder_footprint_frame_zero_slice >> simp[EQ_SYM_EQ]) >>
  `abi_encoder_window_input (AbiComplex infos) (Tuple tys) (ListV avs) (sb+so)
    (rc-so) actual.vs_memory` by
    (drule_all abi_encoder_window_input_suffix_mem_agree >> simp[]) >>
  `abi_footprint_disjoint sb rc
      (abi_decoder_child_scratch (abi_sites_decoder_ids sites first last) b cap actual) /\
   abi_footprint_disjoint d sz
      (abi_decoder_child_scratch (abi_sites_decoder_ids sites first last) b cap actual)` by
    (conj_tac >> irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_sites_encoder_shared_members_pre_def] >>
  qexists_tac `rc` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_members_pre_cons:
  abi_sites_encoder_shared_members_pre sites ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d sz first last b cap s ==>
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_sites_encoder_shared_members_pre sites infos tys avs st src dst sb (so+mem_sz) d sz first last b cap s
Proof
  strip_tac >> qpat_x_assum `abi_sites_encoder_shared_members_pre sites _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_sites_encoder_shared_members_pre_def]) >>
  qpat_x_assum `?rc. _` strip_assume_tac >>
  drule abi_encoder_window_complex_cons >> strip_tac >>
  `so <= rc` by (qpat_x_assum `_ ==> so <= rc` mp_tac >> simp[]) >>
  `infos <> [] ==> so+mem_sz <= rc` by
    (strip_tac >> qpat_x_assum `infos <> [] ==> _` drule >> decide_tac) >>
  `abi_encoder_window_input (AbiComplex infos) (Tuple tys) (ListV avs)
    (sb+(so+mem_sz)) (rc-(so+mem_sz)) s.vs_memory` by
    (qpat_x_assum `abi_encoder_window_input (AbiComplex infos) _ _ _ _ _` mp_tac >>
     `rc - so - mem_sz = rc - (so+mem_sz)` by decide_tac >>
     `sb+so+mem_sz = sb+(so+mem_sz)` by decide_tac >> asm_rewrite_tac []) >>
  asm_simp_tac bool_ss [abi_sites_encoder_shared_members_pre_def] >>
  qexists_tac `rc` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_members_child_buffer:
  abi_sites_encoder_shared_members_pre sites ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d sz first last b cap s /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  eval_operand elem_src s = SOME (n2w (sb+so)) /\ LENGTH (enc ty av) <= sz ==>
  ?child_cap. child_cap <= mem_sz /\
    abi_sites_encoder_shared_input sites (ei,ty,av) (st,elem_src,dst) (sb+so,child_cap) (d,sz)
      (first,last,b,cap) s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_sites_encoder_shared_members_pre sites _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_sites_encoder_shared_members_pre_def]) >>
  qpat_x_assum `?rc. _` strip_assume_tac >>
  drule abi_encoder_window_complex_cons >> strip_tac >>
  `so <= rc` by (qpat_x_assum `_ ==> so <= rc` mp_tac >> simp[]) >>
  qexists_tac `child_cap` >>
  `abi_footprint_disjoint (sb+so) child_cap
    (abi_decoder_child_scratch (abi_sites_decoder_ids sites first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`, `rc`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `regions_disjoint (sb+so,child_cap) (d,sz)` by
    (fs[abi_encoder_zero_aware_separation] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_sites_encoder_shared_input_def] >> decide_tac
QED
