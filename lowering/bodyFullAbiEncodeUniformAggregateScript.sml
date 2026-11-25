Theory bodyFullAbiEncodeUniformAggregate
Ancestors
  bodyFullAbiEncodeUniformMembers exprSimAbiEncodeSourceClosure
  abiEncoderSourceAggregate abiEncoderSourceTransport abiEncoderOpenInput
  abiEncoderInput valueEncodingProofs
  vyperABIRoundtrip vyperTypeDefaults vyperABI vyperValue vyperTypeSystem vyperTypeValues vyperTyping valueEncoding valueEncodingDefs
  vyperValueOperation vyperMisc abiDecodeRanges contractABI list rich_list arithmetic option

Theorem uniform_members_source_reps[local]:
  LENGTH ts = LENGTH infos /\ LENGTH ts = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn. i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type E (EL i ts) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type E (EL i ts)) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type E (EL i ts))) /\
     (!tv v av. evaluate_type E (EL i ts) = SOME tv /\ value_has_type tv v /\
       vyper_to_abi E (EL i ts) v = SOME av ==>
       ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type E (EL i ts)) av /\
         !mem a. val_in_memory tv v a mem ==>
           abi_encoder_open_input ei (EL i cts) rv a (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    (?tv. evaluate_type E (EL i ts) = SOME tv /\ mem_sz = type_memory_size tv)) ==>
  source_reps E ts infos cts
Proof
  simp[source_reps_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _`
    (qspecl_then [`i`,`ei`,`abi_sz`,`mem_sz`,`dyn`] mp_tac) >>
  (impl_tac >- gvs[]) >> simp[source_rep_def] >> metis_tac[]
QED

Theorem abi_encode_uniform_tuple:
  LENGTH ts = LENGTH infos /\ LENGTH ts = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn. i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type E (EL i ts) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type E (EL i ts)) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type E (EL i ts))) /\
     (!tv v av. evaluate_type E (EL i ts) = SOME tv /\ value_has_type tv v /\
       vyper_to_abi E (EL i ts) v = SOME av ==>
       ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type E (EL i ts)) av /\
         !mem a. val_in_memory tv v a mem ==>
           abi_encoder_open_input ei (EL i cts) rv a (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    (?tv. evaluate_type E (EL i ts) = SOME tv /\ mem_sz = type_memory_size tv)) /\
  is_dynamic (vyper_to_abi_type E (TupleT ts)) ==>
  (!tv. evaluate_type E (TupleT ts) = SOME tv ==>
    is_dynamic (Tuple cts) = is_dynamic (vyper_to_abi_type E (TupleT ts)) /\
    abi_member_head_size (Tuple cts) = abi_member_head_size (vyper_to_abi_type E (TupleT ts))) /\
  (!tv v av. evaluate_type E (TupleT ts) = SOME tv /\ value_has_type tv v /\
    vyper_to_abi E (TupleT ts) v = SOME av ==>
    ?rv. enc (Tuple cts) rv = enc (vyper_to_abi_type E (TupleT ts)) av /\
      !mem a. val_in_memory tv v a mem ==>
        abi_encoder_open_input (AbiComplex infos) (Tuple cts) rv a (type_memory_size tv) mem)
Proof
  strip_tac >>
  `source_reps E ts infos cts` by (irule uniform_members_source_reps >> simp[]) >>
  conj_tac >- (drule_all abi_encode_source_tuple >> simp[source_rep_def]) >>
  rpt strip_tac >>
  `?tvs. tv = TupleTV tvs` by gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `!i. i < LENGTH ts ==> evaluate_type E (EL i ts) = SOME (EL i tvs)` by
    (gvs[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP,
         OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_EL, EL_MAP] >>
     rpt strip_tac >>
     qpat_x_assum `!n. _ ==> IS_SOME _` (qspec_then `i` mp_tac) >>
     Cases_on `evaluate_type E (EL i ts)` >> simp[]) >>
  `?rvs. LENGTH rvs = LENGTH ts /\
    !i ei abi_sz mem_sz dyn. i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      enc (EL i cts) (EL i rvs) = enc (vyper_to_abi_type E (EL i ts)) (EL i avs) /\
      !mem a. val_in_memory (EL i tvs) (EL i l) a mem ==>
        abi_encoder_open_input ei (EL i cts) (EL i rvs) a mem_sz mem` by
    (irule abi_encode_uniform_members >> simp[]) >>
  qexists `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
        enc (Tuple (vyper_to_abi_types E ts)) (ListV avs)` by
        (irule abi_encoder_tuple_encoding_cong >>
         drule source_reps_abi_metadata >> strip_tac >>
         simp[source_translation_list] >> rpt strip_tac >>
         Cases_on `EL i infos` >> PairCases_on `r` >>
         first_x_assum drule_all >> simp[EL_MAP]) >>
      gvs[Once enc_def]) >>
  rpt strip_tac >>
  `LENGTH tvs = LENGTH ts` by simp[] >>
  drule_all source_reps_span >> strip_tac >>
  drule_all source_reps_full_span >> strip_tac >>
  irule abi_encoder_source_complex_input >>
  simp[abi_encoder_tuple_type_def, type_memory_size_def, type_memory_size_list_sum] >>
  rpt strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _ ==> enc _ _ = _ /\ _`
    (qspecl_then [`i`,`ei`,`abi_sz`,`mem_sz`,`dyn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> first_x_assum irule >>
  gvs[val_in_memory_def] >> irule abi_encoder_tuple_memory >> simp[]
QED

Theorem abi_encode_uniform_struct:
  FLOOKUP E nsid = SOME (StructArgs args) /\
  LENGTH (MAP SND args) = LENGTH infos /\ LENGTH (MAP SND args) = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn. i < LENGTH (MAP SND args) /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type (E \\ nsid) (EL i (MAP SND args)) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type (E \\ nsid) (EL i (MAP SND args))) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type (E \\ nsid) (EL i (MAP SND args)))) /\
     (!tv v av. evaluate_type (E \\ nsid) (EL i (MAP SND args)) = SOME tv /\ value_has_type tv v /\
       vyper_to_abi (E \\ nsid) (EL i (MAP SND args)) v = SOME av ==>
       ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type (E \\ nsid) (EL i (MAP SND args))) av /\
         !mem a. val_in_memory tv v a mem ==>
           abi_encoder_open_input ei (EL i cts) rv a (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    (?tv. evaluate_type (E \\ nsid) (EL i (MAP SND args)) = SOME tv /\ mem_sz = type_memory_size tv)) /\
  is_dynamic (vyper_to_abi_type E (StructT nsid)) ==>
  (!tv. evaluate_type E (StructT nsid) = SOME tv ==>
    is_dynamic (Tuple cts) = is_dynamic (vyper_to_abi_type E (StructT nsid)) /\
    abi_member_head_size (Tuple cts) = abi_member_head_size (vyper_to_abi_type E (StructT nsid))) /\
  (!tv v av. evaluate_type E (StructT nsid) = SOME tv /\ value_has_type tv v /\
    vyper_to_abi E (StructT nsid) v = SOME av ==>
    ?rv. enc (Tuple cts) rv = enc (vyper_to_abi_type E (StructT nsid)) av /\
      !mem a. val_in_memory tv v a mem ==>
        abi_encoder_open_input (AbiComplex infos) (Tuple cts) rv a (type_memory_size tv) mem)
Proof
  strip_tac >>
  `source_reps (E \\ nsid) (MAP SND args) infos cts` by
    (irule uniform_members_source_reps >> simp[]) >>
  conj_tac >- (drule_all abi_encode_source_struct >> simp[source_rep_def]) >>
  rpt strip_tac >>
  `?tvs. tv = StructTV (ZIP (MAP FST args,tvs)) /\
      evaluate_types (E \\ nsid) (MAP SND args) [] = SOME tvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `struct_has_type _ fields` >>
  drule struct_has_type_values_have_types >>
  drule evaluate_types_length >> strip_tac >>
  simp[MAP_ZIP] >> strip_tac >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `!i. i < LENGTH (MAP SND args) ==>
      evaluate_type (E \\ nsid) (EL i (MAP SND args)) = SOME (EL i tvs)` by
    (gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_EL, EL_MAP] >>
     rpt strip_tac >>
     qpat_x_assum `!n. _ ==> IS_SOME _` (qspec_then `i` mp_tac) >>
     Cases_on `evaluate_type (E \\ nsid) (SND (EL i args))` >> simp[]) >>
  `?rvs. LENGTH rvs = LENGTH (MAP SND args) /\
    !i ei abi_sz mem_sz dyn. i < LENGTH (MAP SND args) /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      enc (EL i cts) (EL i rvs) = enc (vyper_to_abi_type (E \\ nsid) (EL i (MAP SND args))) (EL i avs) /\
      !mem a. val_in_memory (EL i tvs) (EL i (MAP SND fields)) a mem ==>
        abi_encoder_open_input ei (EL i cts) (EL i rvs) a mem_sz mem` by
    (irule abi_encode_uniform_members >> simp[]) >>
  qexists `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
        enc (Tuple (vyper_to_abi_types (E \\ nsid) (MAP SND args))) (ListV avs)` by
        (irule abi_encoder_tuple_encoding_cong >>
         drule source_reps_abi_metadata >> strip_tac >>
         simp[source_translation_list] >> rpt strip_tac >>
         Cases_on `EL i infos` >> PairCases_on `r` >>
         first_x_assum drule_all >> simp[EL_MAP]) >>
      gvs[Once enc_def]) >>
  rpt strip_tac >>
  `LENGTH tvs = LENGTH (MAP SND args)` by simp[] >>
  drule_all source_reps_span >> strip_tac >>
  drule_all source_reps_full_span >> strip_tac >>
  irule abi_encoder_source_complex_input >>
  simp[abi_encoder_tuple_type_def, type_memory_size_def,
       type_memory_size_fields_sum, GSYM MAP_MAP_o, MAP_ZIP] >>
  rpt strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _ ==> enc _ _ = _ /\ _`
    (qspecl_then [`i`,`ei`,`abi_sz`,`mem_sz`,`dyn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> first_x_assum irule >>
  gvs[val_in_memory_def, fields_in_memory_tuple, MAP_ZIP] >>
  irule abi_encoder_tuple_memory >> simp[]
QED

Theorem abi_encode_uniform_sarray:
  LENGTH (REPLICATE n t) = LENGTH infos /\ LENGTH (REPLICATE n t) = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn. i < LENGTH (REPLICATE n t) /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type E (EL i (REPLICATE n t)) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type E (EL i (REPLICATE n t))) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type E (EL i (REPLICATE n t)))) /\
     (!tv v av. evaluate_type E (EL i (REPLICATE n t)) = SOME tv /\ value_has_type tv v /\
       vyper_to_abi E (EL i (REPLICATE n t)) v = SOME av ==>
       ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type E (EL i (REPLICATE n t))) av /\
         !mem a. val_in_memory tv v a mem ==>
           abi_encoder_open_input ei (EL i cts) rv a (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    (?tv. evaluate_type E (EL i (REPLICATE n t)) = SOME tv /\ mem_sz = type_memory_size tv)) /\
  is_dynamic (vyper_to_abi_type E t) ==>
  ?ct.
    (!tv. evaluate_type E (ArrayT t (Fixed n)) = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E (ArrayT t (Fixed n))) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E (ArrayT t (Fixed n)))) /\
    (!tv v av. evaluate_type E (ArrayT t (Fixed n)) = SOME tv /\ value_has_type tv v /\
      vyper_to_abi E (ArrayT t (Fixed n)) v = SOME av ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E (ArrayT t (Fixed n))) av /\
        !mem a. val_in_memory tv v a mem ==>
          abi_encoder_open_input (AbiComplex infos) ct rv a (type_memory_size tv) mem)
Proof
  strip_tac >>
  `source_reps E (REPLICATE n t) infos cts` by
    (irule uniform_members_source_reps >> simp[]) >>
  Cases_on `n = 0`
  >- (gvs[] >> qexists `Array (SOME 0) (Bytes NONE)` >>
      simp[vyper_to_abi_type_def, is_dynamic_def, abi_member_head_size_def] >>
      rpt strip_tac >>
      `?tv0. tv = ArrayTV tv0 (Fixed 0)` by
        gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
      gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
      qexists `ListV []` >> simp[Once enc_def, abi_encoder_dynamic_empty_input]) >>
  drule source_reps_any_dynamic >> strip_tac >>
  `any_dynamic cts` by
    (fs[source_translation_list, any_dynamic_EXISTS, EXISTS_MEM, MEM_REPLICATE] >> metis_tac[]) >>
  qexists `Tuple cts` >> conj_tac
  >- simp[vyper_to_abi_type_def, abi_member_head_size_def, is_dynamic_def] >>
  rpt strip_tac >>
  `?tv0. tv = ArrayTV tv0 (Fixed n)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  rename1 `evaluate_type E t = SOME tv` >>
  `tv0 = tv` by gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  drule_all abi_encoder_sparse_conversion >> strip_tac >>
  `!i. i < LENGTH infos ==> value_has_type tv
      (EL i (array_elements (ArrayTV tv (Fixed (LENGTH infos))) (SArrayV l)))` by
    (rpt strip_tac >> gvs[array_elements_def] >>
     Cases_on `ALOOKUP l i` >> gvs[default_value_well_typed] >>
     drule_all sparse_has_type_lookup >> simp[]) >>
  `LENGTH (array_elements (ArrayTV tv (Fixed (LENGTH infos))) (SArrayV l)) =
    LENGTH infos` by simp[array_elements_def] >>
  `?rvs. LENGTH rvs = LENGTH (REPLICATE (LENGTH infos) t) /\
    !i ei abi_sz mem_sz dyn. i < LENGTH (REPLICATE (LENGTH infos) t) /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      enc (EL i cts) (EL i rvs) = enc (vyper_to_abi_type E (EL i (REPLICATE (LENGTH infos) t))) (EL i avs) /\
      !mem a. val_in_memory (EL i (REPLICATE (LENGTH infos) tv))
        (EL i (array_elements (ArrayTV tv (Fixed (LENGTH infos))) (SArrayV l))) a mem ==>
        abi_encoder_open_input ei (EL i cts) (EL i rvs) a mem_sz mem` by
    (irule abi_encode_uniform_members >> simp[EL_REPLICATE]) >>
  qexists `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
        enc (Tuple (vyper_to_abi_types E (REPLICATE (LENGTH infos) t))) (ListV avs)` by
        (irule abi_encoder_tuple_encoding_cong >>
         drule source_reps_abi_metadata >> strip_tac >>
         simp[source_translation_list] >> rpt strip_tac >>
         Cases_on `EL i infos` >> PairCases_on `r` >>
         qpat_x_assum `!i ei abi_sz mem_sz dyn. _ ==> enc _ _ = _ /\ _`
           (qspecl_then [`i`,`q`,`r0`,`r1`,`r2`] mp_tac) >>
         simp[EL_MAP, EL_REPLICATE]) >>
      gvs[Once enc_def, source_translation_list]) >>
  rpt strip_tac >>
  `value_has_type (ArrayTV tv (Fixed (LENGTH infos))) (ArrayV (SArrayV l))` by
    simp[value_has_type_def] >>
  drule_all abi_encoder_sparse_source >> strip_tac >>
  `!i. i < LENGTH (REPLICATE (LENGTH infos) t) ==>
      evaluate_type E (EL i (REPLICATE (LENGTH infos) t)) =
      SOME (EL i (REPLICATE (LENGTH infos) tv))` by simp[EL_REPLICATE] >>
  `LENGTH (REPLICATE (LENGTH infos) tv) = LENGTH (REPLICATE (LENGTH infos) t)` by simp[] >>
  drule_all source_reps_span >> strip_tac >>
  drule_all source_reps_full_span >> strip_tac >>
  irule abi_encoder_source_complex_input >>
  simp[abi_encoder_tuple_type_def, type_memory_size_def] >>
  rpt strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _ ==> enc _ _ = _ /\ _`
    (qspecl_then [`i`,`ei`,`abi_sz`,`mem_sz`,`dyn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> first_x_assum irule >>
  simp[EL_REPLICATE, REPLICATE_GENLIST, TAKE_GENLIST] >>
  simp[GSYM REPLICATE_GENLIST, MIN_DEF, MULT_COMM]
QED
