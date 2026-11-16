Theory calldataStaticSourceExact
Ancestors
  calldataBulkSourceExact calldataSourceSize calldataSourceDecisions
  calldataReconstruction vyperCalldata vyperCalldataProps
  valueEncodingDefs valueEncoding valueEncodingProps valueEncodingTyping abiDecoderCoherence
  calldataRecursiveProducers compileEnv exprLowering abiEncoder words list arithmetic
  typedMemoryCopy

Theorem calldata_static_elems_lift[local]:
  ~tv_abi_dynamic tv /\
  (!p d mem. mem_bytes_at d (type_memory_size tv) mem =
       mem_bytes_at p (type_memory_size tv) cd ==>
    ?v. cd_decode T cd tv p = SOME v /\ value_has_type tv v /\
      val_in_memory tv v d mem) ==>
  !n i p d mem. mem_bytes_at d (n * type_memory_size tv) mem =
      mem_bytes_at (p+i*type_memory_size tv) (n * type_memory_size tv) cd ==>
    ?vs. cd_decode_elems T cd tv p i n = SOME vs /\ LENGTH vs = n /\
      EVERY (value_has_type tv) vs /\ elems_in_memory vs d tv mem
Proof
  strip_tac >> Induct >> simp[Once cd_decode_def, val_in_memory_def] >>
  rpt strip_tac >>
  `mem_bytes_at d (type_memory_size tv) mem =
    mem_bytes_at (p+i*type_memory_size tv) (type_memory_size tv) cd` by
    (drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`0`,`type_memory_size tv`] mp_tac) >> simp[MULT_CLAUSES]) >>
  `?v. cd_decode T cd tv (p+i*type_memory_size tv) = SOME v /\
    value_has_type tv v /\ val_in_memory tv v d mem` by metis_tac[] >>
  `mem_bytes_at (d+type_memory_size tv) (n*type_memory_size tv) mem =
    mem_bytes_at (p+(i+1)*type_memory_size tv) (n*type_memory_size tv) cd` by
    (qpat_assum `mem_bytes_at _ (SUC n * _) _ = _`
       (mp_then Any mp_tac mem_bytes_at_translated_window) >>
     disch_then (qspecl_then [`type_memory_size tv`,`n*type_memory_size tv`] mp_tac) >>
     simp[MULT_CLAUSES, ADD_CLAUSES, LEFT_ADD_DISTRIB]) >>
  first_x_assum (drule_at Any) >> strip_tac >>
  qexists_tac `v::vs` >>
  simp[Once cd_decode_def, cd_member_ptr_def, cd_at_def, tv_abi_size_def,
    tv_abi_static_memory_size, val_in_memory_def]
QED

Theorem calldata_static_list_lift[local]:
  !ts. EVERY (\tv. ~tv_abi_dynamic tv /\
    !p d mem. mem_bytes_at d (type_memory_size tv) mem =
       mem_bytes_at p (type_memory_size tv) cd ==>
      ?v. cd_decode T cd tv p = SOME v /\ value_has_type tv v /\
        val_in_memory tv v d mem) ts ==>
  !p ofs d mem. mem_bytes_at d (type_memory_size_list ts) mem =
       mem_bytes_at (p+ofs) (type_memory_size_list ts) cd ==>
    ?vs. cd_decode_list T cd ts p ofs = SOME vs /\
      LIST_REL value_has_type ts vs /\ tuple_in_memory vs ts d mem
Proof
  Induct >> simp[Once cd_decode_def, type_memory_size_def, val_in_memory_def] >>
  rpt strip_tac >>
  `mem_bytes_at d (type_memory_size h) mem =
    mem_bytes_at (p+ofs) (type_memory_size h) cd` by
    (drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`0`,`type_memory_size h`] mp_tac) >> simp[]) >>
  `?v. cd_decode T cd h (p+ofs) = SOME v /\ value_has_type h v /\
    val_in_memory h v d mem` by metis_tac[] >>
  `mem_bytes_at (d+type_memory_size h) (type_memory_size_list ts) mem =
    mem_bytes_at (p+(ofs+type_memory_size h)) (type_memory_size_list ts) cd` by
    (qpat_assum `mem_bytes_at _ (_ + _) _ = _`
       (mp_then Any mp_tac mem_bytes_at_translated_window) >>
     disch_then (qspecl_then [`type_memory_size h`,`type_memory_size_list ts`] mp_tac) >>
     simp[NoAsms, AC ADD_ASSOC ADD_COMM]) >>
  qpat_x_assum `EVERY _ ts ==> _` drule >> disch_then drule >> strip_tac >>
  qexists_tac `v::vs` >>
  simp[Once cd_decode_def, cd_member_ptr_def, cd_at_def, tv_abi_size_def,
    tv_abi_static_memory_size, val_in_memory_def]
  >> (gvs[])
QED

Theorem calldata_static_source_exact:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  ~tv_abi_dynamic tv /\ ~tv_needs_clamp tv ==>
  !cd p d mem. mem_bytes_at d (type_memory_size tv) mem =
      mem_bytes_at p (type_memory_size tv) cd ==>
    ?v. cd_decode T cd tv p = SOME v /\ value_has_type tv v /\
      val_wf tv v /\ val_in_memory tv v d mem
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- suspend "scalar"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume calldata_static_source_exact[scalar]:
  rpt strip_tac >>
  `is_word_type (BaseT bt) /\ type_memory_size (BaseTV bt) = 32` by
    (Cases_on `bt` >> gvs[tv_abi_dynamic_def, is_word_type_def, type_memory_size_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[tv_abi_dynamic_def, is_word_type_def, type_memory_size_def,
         abi_decoder_scalar_valid_def]) >>
  `abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt)` by
    simp[abi_decoder_coherent_base_iff] >>
  `~dec_info_needs_clamp (type_to_abi_dec_info sf ce (BaseT bt))` by
    metis_tac[calldata_coherent_clamp] >>
  `mem_word_at d mem = cd_word cd p` by
    gvs[mem_word_at_def, cd_word_def, cd_bytes_def, mem_bytes_at_def] >>
  drule_all calldata_unclamped_word_source >>
  Cases_on `bt` >>
  gvs[Once cd_decode_def, tv_abi_dynamic_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[Once cd_decode_def, tv_abi_dynamic_def]
QED

Resume calldata_static_source_exact[flag]:
  rpt strip_tac >>
  `abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n)` by
    (simp[abi_decoder_coherent_flag_iff] >> metis_tac[]) >>
  `~dec_info_needs_clamp (type_to_abi_dec_info sf ce (FlagT nsid))` by
    metis_tac[calldata_coherent_clamp] >>
  `mem_word_at d mem = cd_word cd p` by
    gvs[type_memory_size_def, mem_word_at_def, cd_word_def, cd_bytes_def, mem_bytes_at_def] >>
  `is_word_type (FlagT nsid)` by simp[is_word_type_def] >>
  drule_all calldata_unclamped_word_source >> simp[Once cd_decode_def]
QED

Resume calldata_static_source_exact[array]:
  rpt strip_tac >> Cases_on `bound` >>
  gvs[tv_abi_dynamic_def, tv_needs_clamp_def, type_memory_size_def] >>
  `?vs. cd_decode_elems T cd tv p 0 n = SOME vs /\ LENGTH vs = n /\
    EVERY (value_has_type tv) vs /\ elems_in_memory vs d tv mem` by
    (irule calldata_static_elems_lift >> simp[] >> metis_tac[]) >>
  qexists_tac `ArrayV (make_array_value tv (Fixed n) vs)` >>
  simp[Once cd_decode_def] >>
  irule calldata_fixed_values_typed_memory >> simp[]
QED

Resume calldata_static_source_exact[tuple]:
  rpt strip_tac >>
  gvs[tv_abi_dynamic_def, tv_needs_clamp_def,
      tv_abi_dynamic_list_exists, tv_needs_clamp_list_exists, type_memory_size_def] >>
  `EVERY (\tv. ~tv_abi_dynamic tv /\
    !p d mem. mem_bytes_at d (type_memory_size tv) mem =
       mem_bytes_at p (type_memory_size tv) cd ==>
      ?v. cd_decode T cd tv p = SOME v /\ value_has_type tv v /\
        val_in_memory tv v d mem) tvs` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN, EXISTS_MEM, MEM_EL] >> metis_tac[]) >>
  drule calldata_static_list_lift >>
  disch_then (qspecl_then [`p`,`0`,`d`,`mem`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `ArrayV (TupleV vs)` >> simp[Once cd_decode_def] >>
  irule calldata_tuple_values_typed_memory >> simp[]
QED

Resume calldata_static_source_exact[struct]:
  rpt strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  gvs[tv_abi_dynamic_def, tv_needs_clamp_def, tv_abi_dynamic_fields_map,
      tv_needs_clamp_fields_map, MAP_ZIP, type_memory_size_def,
      type_memory_size_fields_zip, tv_abi_dynamic_list_exists,
      tv_needs_clamp_list_exists] >>
  `EVERY (\tv. ~tv_abi_dynamic tv /\
    !p d mem. mem_bytes_at d (type_memory_size tv) mem =
       mem_bytes_at p (type_memory_size tv) cd ==>
      ?v. cd_decode T cd tv p = SOME v /\ value_has_type tv v /\
        val_in_memory tv v d mem) tvs` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN, EXISTS_MEM, MEM_EL] >> metis_tac[]) >>
  drule calldata_static_list_lift >>
  disch_then (qspecl_then [`p`,`0`,`d`,`mem`] mp_tac) >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `StructTV (ZIP (names,tvs))` >>
  `LENGTH names = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    (simp[Abbr `names`] >> metis_tac[LIST_REL_LENGTH]) >>
  qexists_tac `StructV (ZIP (names,vs))` >>
  simp[Once cd_decode_def, MAP_ZIP] >>
  irule calldata_struct_values_typed_memory >>
  conj_tac
  >- (gvs[LIST_REL_EL_EQN, EL_ZIP] >> metis_tac[]) >>
  simp[typed_copy_fields_tuple_zip]
QED

Finalise calldata_static_source_exact

Theorem calldata_static_elems_source_exact:
  !ce env sf ty tv cd p d mem n.
    abi_decoder_coherent ce env sf ty tv /\
    ~tv_abi_dynamic tv /\ ~tv_needs_clamp tv /\
    mem_bytes_at d (n * type_memory_size tv) mem =
      mem_bytes_at p (n * type_memory_size tv) cd ==>
    ?vs. cd_decode_elems T cd tv p 0 n = SOME vs /\ LENGTH vs = n /\
      EVERY (value_has_type tv) vs /\ elems_in_memory vs d tv mem
Proof
  rpt strip_tac >> irule calldata_static_elems_lift >> simp[] >>
  rpt strip_tac >> drule_all calldata_static_source_exact >> metis_tac[]
QED
