Theory exprSimAbiDecodeMinimumLayout
Ancestors
  abiCallerAbiShape abiDecoderCoherence abiDecodeRanges compileEnv vyperABI contractABI list

Theorem abi_decode_coherent_shape:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_caller_abi_shape sf env ty
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- simp[abi_caller_abi_shape_base]
  >- (rpt strip_tac >>
      simp[abi_caller_abi_shape_def, is_abi_dynamic_def, abi_static_size_def,
           vyper_to_abi_type_def, is_dynamic_def, static_length_def])
  >- (rpt strip_tac >> irule abi_caller_abi_shape_array >> simp[])
  >- (rpt strip_tac >> irule abi_caller_abi_shape_tuple >>
      gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[])
  >> rpt strip_tac >> irule abi_caller_abi_shape_struct >>
  qexistsl_tac [`args`, `fields`] >> simp[] >>
  gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]
QED

Theorem abi_decode_shape_member_head[local]:
  abi_caller_abi_shape sf env ty ==>
  (if is_abi_dynamic sf ty then 32 else abi_static_size sf ty) =
    abi_member_head_size (vyper_to_abi_type env ty)
Proof
  simp[abi_caller_abi_shape_def, abi_member_head_size_def] >> metis_tac[]
QED

Theorem abi_decode_shape_list_heads[local]:
  !tys. EVERY (abi_caller_abi_shape sf env) tys ==>
    SUM (MAP (\t. if is_abi_dynamic sf t then 32 else abi_static_size sf t) tys) =
    head_lengths (vyper_to_abi_types env tys) 0
Proof
  Induct >> simp[head_lengths_acc] >> rpt strip_tac >>
  drule abi_decode_shape_member_head >> simp[]
QED

Theorem abi_decode_coherent_minimum:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_static_size sf ty = abi_static_length (vyper_to_abi_type env ty)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ty` >>
  gvs[abi_decoder_coherent_base_iff, abi_decoder_coherent_tuple_iff,
      abi_decoder_coherent_array_iff, abi_decoder_coherent_struct_iff,
      abi_decoder_coherent_flag_iff]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
      simp[abi_static_size_def, vyper_base_to_abi_type_def, abi_static_length_def])
  >- suspend "tuple"
  >- (rename1 `ArrayT elem bound` >>
      qpat_x_assum `abi_decoder_coherent _ _ _ elem _`
        (mp_tac o MATCH_MP abi_decode_coherent_shape) >>
      simp[abi_caller_abi_shape_def] >> strip_tac >>
      Cases_on `bound` >> simp[abi_static_size_def, abi_static_length_def] >> metis_tac[])
  >- suspend "struct"
  >> simp[abi_static_size_def, vyper_to_abi_type_def,
        abi_static_length_def, static_length_def]
QED
Resume abi_decode_coherent_minimum[tuple]:
  rename1 `TupleT tys` >> rpt strip_tac >>
  `EVERY (abi_caller_abi_shape sf env) tys` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[abi_decode_coherent_shape]) >>
  simp[abi_static_size_def, abi_static_length_def] >>
  irule abi_decode_shape_list_heads >> simp[]
QED
Resume abi_decode_coherent_minimum[struct]:
  rename1 `StructT nsid` >>
  `MAP SND (MAP (\(name,ty,sz). (name,ty)) fields) = MAP (FST o SND) fields` by
    simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
  `EVERY (abi_caller_abi_shape (sf \\ nsid_to_string nsid) (env \\ nsid))
     (MAP (FST o SND) fields)` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[abi_decode_coherent_shape]) >>
  simp[abi_static_size_def, abi_static_length_def, vyper_to_abi_type_def] >>
  irule abi_decode_shape_list_heads >> simp[]
QED
Finalise abi_decode_coherent_minimum
