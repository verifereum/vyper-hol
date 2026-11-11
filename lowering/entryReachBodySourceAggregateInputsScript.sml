Theory entryReachBodySourceAggregateInputs
Ancestors
  valueEncodingDefs entryReachBodySourceMemberEntry entryReachBodyConversionSupport entryReachBodySourceInverse
  abiDecoderCoherence abiDecoderMembers abiDecoderMemberInfos abiDecoderEmpty abiDecoderOffset
  abiEncoderSourceTransport abiDecoderFixedMemory abiDecoderStruct abiCanonicalHeadSize
  vyperABI vyperTyping vyperValue vyperTypeDefaults vyperValueOperation
  valueEncodingTyping abiStaticDynarrayLayout valueEncodingProps valueEncoding valueEncodingProofs contractABI compileEnv list rich_list alist pair

Theorem entry_source_members_intro:
  !tys tvs avs vs.
  EVERY (entry_abi_support env) tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\
  vyper_to_abi_list env tys vs = SOME avs ==>
  entry_source_members ce env sf tys tvs avs vs
Proof
  Induct >> rpt gen_tac >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def] >> rpt strip_tac >>
  gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  simp[entry_source_metadata_def] >>
  metis_tac[abi_decoder_coherent_header, abi_decoder_header_def]
QED

Theorem entry_source_tuple_members:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  entry_source_metadata ce env sf (TupleT tys) (TupleTV tvs) di av v ==>
  ?avs vs. av = ListV avs /\ v = ArrayV (TupleV vs) /\
    entry_source_members ce env sf tys tvs avs vs
Proof
  strip_tac >>
  gvs[entry_source_metadata_def, abi_decoder_coherent_tuple_iff, Excl "enc_def"] >>
  Cases_on `v` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
  Cases_on `a` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  irule entry_source_members_intro >>
  gvs[entry_abi_support_tuple, values_have_types_LIST_REL, Excl "enc_def"]
QED

Theorem entry_source_members_lengths:
  !tys tvs avs vs. entry_source_members ce env sf tys tvs avs vs ==>
  LENGTH tys = LENGTH tvs /\ LENGTH tys = LENGTH avs /\ LENGTH tys = LENGTH vs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def] >> metis_tac[]
QED

Theorem entry_source_members_memory_sizes:
  !tys tvs avs vs. entry_source_members ce env sf tys tvs avs vs ==>
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def, entry_source_metadata_def] >> metis_tac[]
QED

Theorem entry_source_tuple_inputs:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  entry_source_metadata ce env sf (TupleT tys) (TupleTV tvs) di av v ==>
  ?avs vs. av = ListV avs /\ v = ArrayV (TupleV vs) /\
    entry_source_members ce env sf tys tvs avs vs /\
    LENGTH tys = LENGTH tvs /\ LENGTH tys = LENGTH avs /\ LENGTH tys = LENGTH vs /\
    di = DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
      (abi_decoder_member_infos sf ce tys) /\
    vyper_to_abi_type env (TupleT tys) = Tuple (MAP (vyper_to_abi_type env) tys) /\
    type_memory_size (TupleTV tvs) = SUM (MAP (type_memory_bytes ce) tys) /\
    (!d mem. val_in_memory (TupleTV tvs) v d mem = tuple_in_memory vs tvs d mem)
Proof
  strip_tac >> drule_all entry_source_tuple_members >> strip_tac >>
  drule entry_source_members_lengths >> strip_tac >>
  drule entry_source_members_memory_sizes >> strip_tac >>
  gvs[entry_source_metadata_def, abi_decoder_tuple_infos, vyper_to_abi_type_def,
      vyper_to_abi_types_MAP, type_memory_size_def, type_memory_size_list_sum,
      val_in_memory_tuple, Excl "enc_def"]
QED

Theorem entry_source_struct_members:
  abi_decoder_coherent ce env sf (StructT nsid) tv /\
  entry_source_metadata ce env sf (StructT nsid) tv di av v ==>
  ?args fields tvs avs vals.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
    tv = StructTV (ZIP (MAP FST args,tvs)) /\
    av = ListV avs /\ v = StructV vals /\
    entry_source_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs avs (MAP SND vals)
Proof
  strip_tac >>
  gvs[abi_decoder_coherent_struct_iff, entry_source_metadata_def, Excl "enc_def"] >>
  Cases_on `v` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  qexists `tvs` >> simp[] >>
  irule entry_source_members_intro >> simp[] >>
  conj_tac
  >- gvs[entry_abi_support_struct, EVERY_MAP, Excl "enc_def"] >>
  simp[GSYM values_have_types_LIST_REL] >>
  drule struct_has_type_values_have_types >>
  drule LIST_REL_LENGTH >> simp[MAP_ZIP]
QED

Theorem source_members_indexed_intro[local]:
  !tys tvs avs vs.
  LENGTH tys = LENGTH tvs /\ LENGTH tys = LENGTH avs /\ LENGTH tys = LENGTH vs /\
  (!i. i < LENGTH tys ==>
    abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
    entry_source_metadata ce env sf (EL i tys) (EL i tvs)
      (type_to_abi_dec_info sf ce (EL i tys)) (EL i avs) (EL i vs)) ==>
  entry_source_members ce env sf tys tvs avs vs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def] >> rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem entry_source_fixed_members:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  entry_source_metadata ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v ==>
  ?avs kvs.
    av = ListV avs /\ v = ArrayV (SArrayV kvs) /\ LENGTH avs = n /\
    entry_source_members ce env sf (REPLICATE n ty) (REPLICATE n tv) avs
      (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))
Proof
  strip_tac >>
  gvs[abi_decoder_coherent_array_iff, entry_source_metadata_def, Excl "enc_def"] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  Cases_on `v` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
  Cases_on `a` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  drule_all abi_encoder_sparse_conversion >> strip_tac >> simp[] >>
  `entry_abi_support env ty` by gvs[entry_abi_support_array, Excl "enc_def"] >>
  `!i. i < LENGTH avs ==> value_has_type tv
    (EL i (array_elements (ArrayTV tv (Fixed (LENGTH avs))) (SArrayV l)))` by
    (simp[array_elements_def] >> rpt strip_tac >>
     Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[default_value_has_type_thm] >>
     drule sparse_has_type_all_have_type >>
     simp[all_have_type_EVERY, EVERY_MAP, EVERY_MEM] >>
     metis_tac[ALOOKUP_MEM, SND]) >>
  irule source_members_indexed_intro >>
  simp[array_elements_def, EL_REPLICATE, entry_source_metadata_def] >>
  gvs[array_elements_def]
QED

Theorem entry_source_empty_descriptor_value:
  abi_decoder_coherent ce env sf ty tv /\
  entry_source_metadata ce env sf ty tv di av v /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] ==>
  type_memory_bytes ce ty = 0 /\ type_memory_size tv = 0 /\
  (!d mem. val_in_memory tv v d mem)
Proof
  strip_tac >>
  gvs[abi_decoder_empty_dynamic_translation, abi_decoder_coherent_array_iff] >>
  `abi_decoder_coherent ce env sf (ArrayT elem (Fixed 0)) (ArrayTV tv' (Fixed 0))` by
    simp[abi_decoder_coherent_array_iff] >>
  drule_all entry_source_fixed_members >> strip_tac >>
  drule entry_source_members_lengths >>
  simp[array_elements_def] >> strip_tac >>
  gvs[entry_source_metadata_def, Once value_has_type_def, Excl "enc_def"] >>
  gvs[value_has_type_def, val_in_memory_def, type_memory_bytes_def, type_memory_size_def] >>
  drule sparse_has_type_all_less >> Cases_on `kvs` >>
  simp[val_in_memory_def]
QED

Theorem source_members_forward[local]:
  !tys tvs avs vs. entry_source_members ce env sf tys tvs avs vs ==>
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME avs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def, entry_source_metadata_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once vyper_to_abi_def] >> metis_tac[]
QED

Theorem entry_source_fixed_inputs:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  entry_source_metadata ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v ==>
  ?avs vs. av = ListV avs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\
    LENGTH avs = n /\ LENGTH vs = n /\
    entry_source_members ce env sf (REPLICATE n ty) (REPLICATE n tv) avs vs /\
    di = DecComplex (is_abi_dynamic ce.ce_struct_fields ty)
      (abi_decoder_member_infos sf ce (REPLICATE n ty)) /\
    enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av =
      enc (Tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))) (ListV avs) /\
    type_memory_size (ArrayTV tv (Fixed n)) =
      SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) /\
    (!d mem. tuple_in_memory vs (REPLICATE n tv) d mem ==> val_in_memory (ArrayTV tv (Fixed n)) v d mem)
Proof
  strip_tac >> drule_all entry_source_fixed_members >> strip_tac >>
  drule source_members_forward >> strip_tac >>
  drule_all entry_source_list_conversion_inverse >> strip_tac >>
  `abi_to_vyper env (ArrayT ty (Fixed n)) av = SOME v` by
    (irule entry_source_conversion_inverse >>
     gvs[entry_source_metadata_def, Excl "enc_def"] >> metis_tac[]) >>
  `evaluate_type env ty = SOME tv` by
    (gvs[abi_decoder_coherent_array_iff] >>
     metis_tac[abi_decoder_coherent_header, abi_decoder_header_def]) >>
  drule entry_source_members_lengths >> strip_tac >>
  drule entry_source_members_memory_sizes >> strip_tac >>
  `v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0
    (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))))` by
    (qpat_x_assum `abi_to_vyper env (ArrayT _ _) _ = _` mp_tac >>
     asm_simp_tac bool_ss [Once abi_to_vyper_def, compatible_bound_def, make_array_value_def, LET_THM] >>
     simp[Excl "enc_def"]) >>
  qexistsl [`avs`, `array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)`] >>
  asm_rewrite_tac[] >>
  conj_tac >- gvs[Excl "enc_def"] >>
  conj_tac
  >- gvs[entry_source_metadata_def, abi_decoder_fixed_array_infos, Excl "enc_def"] >>
  conj_tac
  >- simp[vyper_to_abi_type_def, canonical_array_tuple, map_replicate, Excl "enc_def"] >>
  conj_tac
  >- gvs[type_memory_size_def, type_memory_size_list_sum, map_replicate, SUM_REPLICATE,
         entry_source_metadata_def, Once type_memory_bytes_def, Excl "enc_def"] >>
  rpt strip_tac >> irule abi_decoder_fixed_array_memory >> simp[]
QED

Theorem entry_source_struct_inputs:
  abi_decoder_coherent ce env sf (StructT nsid) tv /\
  entry_source_metadata ce env sf (StructT nsid) tv di av v ==>
  ?args fields tvs avs vals.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    tv = StructTV (ZIP (MAP FST args,tvs)) /\ av = ListV avs /\ v = StructV vals /\
    entry_source_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs avs (MAP SND vals) /\
    LENGTH args = LENGTH tvs /\ LENGTH args = LENGTH avs /\ LENGTH args = LENGTH vals /\
    di = DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args))
      (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args)) /\
    vyper_to_abi_type env (StructT nsid) =
      Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) /\
    type_memory_size tv = SUM (MAP (type_memory_bytes ce) (MAP SND args)) /\
    (!d mem. tuple_in_memory (MAP SND vals) tvs d mem ==> val_in_memory tv v d mem)
Proof
  strip_tac >> drule_all entry_source_struct_members >> strip_tac >>
  drule entry_source_members_lengths >> strip_tac >>
  drule entry_source_members_memory_sizes >> strip_tac >>
  qexistsl [`args`, `fields`, `tvs`, `avs`, `vals`] >> asm_rewrite_tac[] >>
  conj_tac >- gvs[Excl "enc_def"] >>
  conj_tac >- gvs[Excl "enc_def"] >>
  conj_tac >- gvs[Excl "enc_def"] >>
  conj_tac
  >- (drule_all abi_decoder_struct_field_types >> strip_tac >>
      `type_to_abi_dec_info sf ce (StructT nsid) =
        DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args))
          (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args))` by
        (drule abi_decoder_struct_infos >> disch_then (qspec_then `ce` mp_tac) >>
         gvs[Excl "enc_def"]) >>
      gvs[entry_source_metadata_def, Excl "enc_def"]) >>
  conj_tac
  >- simp[vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> gvs[Excl "enc_def"]) >>
  conj_tac >- simp[type_memory_size_def, type_memory_size_list_sum] >>
  simp[val_in_memory_struct] >> rpt strip_tac >>
  irule static_fields_memory_zip >>
  gvs[entry_source_metadata_def, Once value_has_type_def, Excl "enc_def"]
QED
