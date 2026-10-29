(* Open source transport through physical scratch effects. *)
Theory abiEncoderSharedInputEffect
Ancestors
  abiEncoderSharedContract abiEncoderOpenInputFrame abiEncoderZeroFrame abiScratchEffect
  abiScratchFootprint abiScratchEncoderContract abiDecoderFrame abiDecoderFootprint abiDecoderAllocation abiDecoderReentry
  compileEnv venomState venomMemDefs valueEncoding words list arithmetic

Theorem abi_encoder_shared_input_effect:
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz)
    (first,last,b,cap) initial /\
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
  first <= lo /\ hi <= last /\ st.cs_next_var <= next ==>
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz)
    (first,last,b,cap) actual
Proof
  strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual` by
    (drule_all abi_scratch_effect_frame >> simp[]) >>
  `mem_bytes_at sb source_cap initial.vs_memory = mem_bytes_at sb source_cap actual.vs_memory` by
    (drule_all abi_encoder_footprint_frame_zero_slice >> simp[]) >>
  `abi_encoder_open_input ei at av sb source_cap actual.vs_memory` by
    (drule_all abi_encoder_open_input_mem_agree >> simp[]) >>
  `abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (metis_tac[abi_scratch_effect_operand]) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    fs[abi_scratch_effect_def] >>
  `abi_footprint_disjoint sb source_cap
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
   abi_footprint_disjoint d sz
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (conj_tac >> irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_shared_input_def]
QED

Theorem abi_encoder_shared_input_mono:
  abi_encoder_shared_input (ei,at,av) (st,src,dst) src_region dst_region arena s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_shared_input (ei,at,av) (prepared,src,dst) src_region dst_region arena s
Proof
  PairCases_on `src_region` >> PairCases_on `dst_region` >> PairCases_on `arena` >>
  simp_tac bool_ss [abi_encoder_shared_input_def] >> strip_tac >>
  asm_simp_tac bool_ss [] >> conj_tac >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> simp[]
QED
