Theory ctorDeployMemoryRunMemEntryAggregate
Ancestors
  vyperABI contractABI list rich_list arithmetic vyperTyping vyperValue valueEncoding supportedTypes
  ctorDeployMemoryRunMemEntrySupported ctorDeployMemoryRunMemEntryDefaults
  ctorDeployMemoryRunMemEntrySparse ctorDeployMemoryRunMemEntryAggregateProbe
Libs
  wordsLib

Theorem ctor_conversion_list_lift:
  !ts vs avs.
    LIST_REL (\ty v. !av. vyper_to_abi env ty v = SOME av ==>
      has_type (vyper_to_abi_type env ty) av /\
      abi_to_vyper env ty av = SOME v) ts vs /\
    vyper_to_abi_list env ts vs = SOME avs ==>
    LIST_REL has_type (MAP (vyper_to_abi_type env) ts) avs /\
    abi_to_vyper_list env ts avs = SOME vs
Proof
  Induct >> Cases_on `vs` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem ctor_scalar_list_alignment:
  !ts tvs vs.
    EVERY supported_scalar_type ts /\
    OPT_MMAP (evaluate_type env) ts = SOME tvs /\
    values_have_types tvs vs /\ tuple_val_wf vs tvs ==>
    LIST_REL (\ty v. !av. vyper_to_abi env ty v = SOME av ==>
      has_type (vyper_to_abi_type env ty) av /\
      abi_to_vyper env ty av = SOME v) ts vs
Proof
  Induct >> Cases_on `vs` >> Cases_on `tvs` >>
  simp[evaluate_type_def, value_has_type_def, val_wf_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[ctor_supported_scalar_strict_type, ctor_supported_scalar_inverse]
QED

Theorem ctor_supported_scalar_list_conversion:
  EVERY supported_scalar_type ts /\
  OPT_MMAP (evaluate_type env) ts = SOME tvs /\
  values_have_types tvs vs /\ tuple_val_wf vs tvs /\
  vyper_to_abi_list env ts vs = SOME avs ==>
  LIST_REL has_type (MAP (vyper_to_abi_type env) ts) avs /\
  abi_to_vyper_list env ts avs = SOME vs
Proof
  strip_tac >> irule ctor_conversion_list_lift >>
  conj_tac >- simp[] >> irule ctor_scalar_list_alignment >> metis_tac[]
QED

Theorem ctor_conversion_same_lift:
  !vs avs.
    EVERY (\v. !av. vyper_to_abi env ty v = SOME av ==>
      has_type (vyper_to_abi_type env ty) av /\
      abi_to_vyper env ty av = SOME v) vs /\
    vyper_to_abi_same env ty vs = SOME avs ==>
    EVERY (has_type (vyper_to_abi_type env ty)) avs /\
    abi_to_vyper_list env (REPLICATE (LENGTH vs) ty) avs = SOME vs
Proof
  Induct >> simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem ctor_abi_types_map:
  !ts. vyper_to_abi_types env ts = MAP (vyper_to_abi_type env) ts
Proof
  Induct >> simp[]
QED


Theorem ctor_supported_tuple_inverse:
  EVERY supported_scalar_type ts /\
  evaluate_type env (TupleT ts) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  vyper_to_abi env (TupleT ts) v = SOME av ==>
  abi_to_vyper env (TupleT ts) av = SOME v
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >>
  rename1 `ArrayV a` >> Cases_on `a` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, value_has_type_def, val_wf_def,
      evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  drule_all ctor_supported_scalar_list_conversion >> simp[]
QED

Theorem ctor_scalar_same_alignment:
  !vs. supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
    all_have_type tv vs /\ elems_val_wf vs tv ==>
    EVERY (\v. !av. vyper_to_abi env ty v = SOME av ==>
      has_type (vyper_to_abi_type env ty) av /\
      abi_to_vyper env ty av = SOME v) vs
Proof
  Induct >> simp[value_has_type_def, val_wf_def] >> rpt strip_tac >>
  metis_tac[ctor_supported_scalar_strict_type, ctor_supported_scalar_inverse]
QED

Theorem ctor_same_conversion_length:
  !vs avs. vyper_to_abi_same env ty vs = SOME avs ==>
    LENGTH avs = LENGTH vs
Proof
  Induct >> simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem ctor_supported_dynamic_inverse:
  supported_scalar_type ty /\
  evaluate_type env (ArrayT ty (Dynamic n)) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  vyper_to_abi env (ArrayT ty (Dynamic n)) v = SOME av ==>
  abi_to_vyper env (ArrayT ty (Dynamic n)) av = SOME v
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >>
  rename1 `ArrayV a` >> Cases_on `a` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, value_has_type_def, val_wf_def, AllCaseEqs()] >>
  drule_all ctor_scalar_same_alignment >> strip_tac >>
  drule_all ctor_conversion_same_lift >> strip_tac >>
  `LENGTH avs = LENGTH l` by
    (drule ctor_same_conversion_length >> simp[]) >>
  simp[compatible_bound_def, make_array_value_def]
QED

Theorem ctor_scalar_fields_alignment:
  !names tvs fields.
    struct_has_type (ZIP (names,tvs)) fields /\
    LENGTH names = LENGTH tvs /\ fields_val_wf fields (ZIP (names,tvs)) ==>
    values_have_types tvs (MAP SND fields) /\
    tuple_val_wf (MAP SND fields) tvs /\
    ZIP (names, MAP SND fields) = fields
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fields` >>
  simp[value_has_type_def, val_wf_def] >>
  rename1 `struct_has_type _ (p::rest)` >> PairCases_on `p` >>
  simp[value_has_type_def, val_wf_def] >> rpt strip_tac >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem ctor_supported_struct_inverse_fields:
  FLOOKUP env id = SOME (StructArgs args) /\
  EVERY supported_scalar_type (MAP SND args) /\
  evaluate_type env (StructT id) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  vyper_to_abi env (StructT id) v = SOME av ==>
  abi_to_vyper env (StructT id) av = SOME v
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (imp_res_tac vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  gvs[value_has_type_def, val_wf_def] >>
  drule ctor_scalar_fields_alignment >> simp[] >> strip_tac >>
  drule_all ctor_supported_scalar_list_conversion >> simp[]
QED

Theorem ctor_sparse_scalar_alignment:
  !sparse. sparse_has_type tv n sparse /\ kvs_val_wf sparse tv n ==>
    EVERY (\(k,v). k < n /\ v <> default_value tv /\
      value_has_type tv v /\ val_wf tv v) sparse
Proof
  Induct >> simp[value_has_type_def, val_wf_def] >>
  gen_tac >> PairCases_on `h` >> simp[value_has_type_def, val_wf_def] >>
  metis_tac[]
QED

Theorem ctor_scalar_sparse_point_inverse:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  sparse_has_type tv n sparse /\ kvs_val_wf sparse tv n /\
  vyper_to_abi_sparse env ty tv n sparse = SOME avs /\ k < n ==>
  abi_to_vyper env ty (EL k avs) =
    SOME (case ALOOKUP sparse k of NONE => default_value tv | SOME v => v)
Proof
  strip_tac >> Cases_on `ALOOKUP sparse k`
  >- (drule_all ctor_canonical_sparse_absent >> simp[] >>
      metis_tac[ctor_supported_scalar_default_inverse]) >>
  drule_all abiStaticSparsePropsTheory.canonical_sparse_lookup >> strip_tac >>
  drule_all ctor_sparse_scalar_alignment >>
  simp[EVERY_MEM] >> strip_tac >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  metis_tac[ctor_supported_scalar_inverse]
QED

Theorem ctor_pointwise_decode_list:
  !avs dense. LENGTH dense = LENGTH avs /\
    (!k. k < LENGTH avs ==>
      abi_to_vyper env ty (EL k avs) = SOME (EL k dense)) ==>
    abi_to_vyper_list env (REPLICATE (LENGTH avs) ty) avs = SOME dense
Proof
  Induct >> Cases_on `dense` >> simp[] >> rpt strip_tac >>
  `abi_to_vyper env ty h' = SOME h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `abi_to_vyper_list env (REPLICATE (LENGTH avs) ty) avs = SOME t` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]) >> simp[]
QED

Theorem ctor_supported_fixed_inverse:
  supported_scalar_type ty /\
  evaluate_type env (ArrayT ty (Fixed n)) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  vyper_to_abi env (ArrayT ty (Fixed n)) v = SOME av ==>
  abi_to_vyper env (ArrayT ty (Fixed n)) av = SOME v
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >>
  rename1 `ArrayV a` >> Cases_on `a` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, value_has_type_def, val_wf_def, AllCaseEqs()] >>
  imp_res_tac abiStaticSparsePropsTheory.canonical_sparse_length >>
  qmatch_asmsub_rename_tac `sparse_has_type elem n sparse` >>
  qabbrev_tac `dense = GENLIST (\k. case ALOOKUP sparse k of
    NONE => default_value elem | SOME v => v) n` >>
  `LENGTH dense = n` by simp[Abbr `dense`] >>
  `abi_to_vyper_list env (REPLICATE (LENGTH avs) ty) avs = SOME dense` by
    (irule ctor_pointwise_decode_list >> simp[] >> rpt strip_tac >>
     simp[Abbr `dense`, EL_GENLIST] >>
     irule ctor_scalar_sparse_point_inverse >> metis_tac[]) >>
  `enumerate_static_array (default_value elem) 0 dense = sparse` by
    (irule ctor_enumerate_sparse_reconstruct >>
     simp[Abbr `dense`, EL_GENLIST] >>
     drule_all ctor_sparse_scalar_alignment >> strip_tac >>
     gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> PairCases_on `e` >> simp[]) >>
  simp[compatible_bound_def, make_array_value_def]
QED

Theorem ctor_supported_struct_lookup:
  !tops id args. supported_struct_fields tops id = SOME args ==>
    FLOOKUP (type_env tops) id = SOME (StructArgs args)
Proof
  Induct >> Cases_on `id` >>
  simp[supported_struct_fields_def, vyperContextTheory.type_env_def] >>
  Cases_on `h` >>
  simp[supported_struct_fields_def, vyperContextTheory.type_env_for_module_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  fs[vyperContextTheory.type_env_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem ctor_supported_value_inverse:
  supported_value_type tops ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  vyper_to_abi (type_env tops) ty v = SOME av ==>
  abi_to_vyper (type_env tops) ty av = SOME v
Proof
  strip_tac >>
  Cases_on `supported_scalar_type ty`
  >- metis_tac[ctor_supported_scalar_inverse] >>
  fs[supported_value_type_def] >> Cases_on `ty` >>
  gvs[AllCaseEqs()]
  >- metis_tac[ctor_supported_tuple_inverse]
  >- (Cases_on `b` >> gvs[] >>
      metis_tac[ctor_supported_fixed_inverse, ctor_supported_dynamic_inverse,
        supported_scalar_type_def]) >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  drule ctor_supported_struct_lookup >> strip_tac >>
  irule ctor_supported_struct_inverse_fields >>
  simp[] >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[supported_scalar_type_def]
QED

Theorem ctor_supported_scalar_memory_lower:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv ==>
  32 <= type_memory_size tv
Proof
  Cases_on `ty` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
       evaluate_type_def, type_memory_size_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), type_memory_size_def] >>
  Cases_on `b` >> gvs[type_memory_size_def, AllCaseEqs()]
QED

Theorem ctor_scalar_list_memory_lower:
  !ts tvs. EVERY supported_scalar_type ts /\
    OPT_MMAP (evaluate_type env) ts = SOME tvs ==>
    32 * LENGTH tvs <= type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all ctor_supported_scalar_memory_lower >> strip_tac >>
  simp[type_memory_size_def] >> decide_tac
QED

Theorem ctor_tuple_conversion_length:
  !ts vs avs. vyper_to_abi_list env ts vs = SOME avs ==>
    LENGTH avs = LENGTH ts
Proof
  Induct >> Cases_on `vs` >> simp[Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem ctor_supported_tuple_length_bound:
  EVERY supported_scalar_type ts /\
  evaluate_type env (TupleT ts) = SOME tv /\
  type_memory_size tv < 2 ** 64 /\
  vyper_to_abi env (TupleT ts) v = SOME (ListV avs) ==>
  LENGTH avs < 2 ** 256
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >>
  rename1 `ArrayV a` >> Cases_on `a` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  drule_all ctor_scalar_list_memory_lower >> strip_tac >>
  drule ctor_tuple_conversion_length >> strip_tac >>
  imp_res_tac vyperTypeABITheory.OPT_MMAP_LENGTH >>
  gvs[type_memory_size_def] >> decide_tac
QED


Theorem ctor_positive_product_lower[local]:
  !n m:num. 1 <= m ==> n <= n * m
Proof
  rpt strip_tac >> once_rewrite_tac[GSYM MULT_RIGHT_1] >> simp[LE_MULT_LCANCEL]
QED

Theorem ctor_bounded_product[local]:
  !n m B:num. 1 <= m /\ n * m < B ==> n < B
Proof
  metis_tac[ctor_positive_product_lower, LESS_EQ_LESS_TRANS]
QED

Theorem ctor_bounded_product_offset[local]:
  !n m B:num. 1 <= m /\ n * m + 32 < B ==> n < B
Proof
  rpt strip_tac >> irule ctor_bounded_product >>
  qexists `m` >> simp[] >>
  irule LESS_EQ_LESS_TRANS >> qexists `n*m+32` >> simp[]
QED

Theorem ctor_supported_array_length_bound:
  supported_scalar_type ty /\
  evaluate_type env (ArrayT ty bd) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_size tv < 2 ** 64 /\
  vyper_to_abi env (ArrayT ty bd) v = SOME (ListV avs) ==>
  LENGTH avs < 2 ** 256
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >>
  rename1 `ArrayV a` >> Cases_on `a` >> Cases_on `bd` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, value_has_type_def, val_wf_def, AllCaseEqs()] >>
  drule_all ctor_supported_scalar_memory_lower >> strip_tac >>
  imp_res_tac abiStaticSparsePropsTheory.canonical_sparse_length >>
  imp_res_tac ctor_same_conversion_length >>
  gvs[type_memory_size_def] >>
  `1 <= type_memory_size tv'` by decide_tac >>
  imp_res_tac ctor_bounded_product >>
  imp_res_tac ctor_bounded_product_offset >> decide_tac
QED

Theorem ctor_fields_memory_zip:
  !names tvs. LENGTH names = LENGTH tvs ==>
    type_memory_size_fields (ZIP (names,tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def]
QED

Theorem ctor_supported_struct_length_bound:
  FLOOKUP env id = SOME (StructArgs args) /\
  EVERY supported_scalar_type (MAP SND args) /\
  evaluate_type env (StructT id) = SOME tv /\
  type_memory_size tv < 2 ** 64 /\
  vyper_to_abi env (StructT id) v = SOME (ListV avs) ==>
  LENGTH avs < 2 ** 256
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (imp_res_tac vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  drule_all ctor_scalar_list_memory_lower >> strip_tac >>
  drule ctor_tuple_conversion_length >> strip_tac >>
  gvs[type_memory_size_def, ctor_fields_memory_zip] >> decide_tac
QED

Theorem ctor_scalar_conversion_not_list:
  supported_scalar_type ty /\ vyper_to_abi env ty v = SOME (ListV avs) ==> F
Proof
  Cases_on `ty` >>
  simp[supported_scalar_type_def, supported_word_type_def, supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> Cases_on `v` >>
  simp[Once vyper_to_abi_def, supported_word_type_def, supported_string_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ctor_supported_aggregate_length_bound:
  supported_value_type tops ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ type_memory_size tv < 2 ** 64 /\
  vyper_to_abi (type_env tops) ty v = SOME (ListV avs) ==>
  LENGTH avs < 2 ** 256
Proof
  strip_tac >>
  Cases_on `supported_scalar_type ty`
  >- metis_tac[ctor_scalar_conversion_not_list] >>
  fs[supported_value_type_def] >> Cases_on `ty` >> gvs[AllCaseEqs()]
  >- (drule_all (SRULE [] ctor_supported_tuple_length_bound) >> simp[])
  >- (Cases_on `b` >> gvs[] >>
      metis_tac[SRULE [] ctor_supported_array_length_bound, supported_scalar_type_def]) >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  drule ctor_supported_struct_lookup >> strip_tac >>
  irule (SRULE [] ctor_supported_struct_length_bound) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists `v` >> simp[] >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[supported_scalar_type_def]
QED

Theorem ctor_supported_tuple_strict_bounded:
  EVERY supported_scalar_type ts /\ evaluate_type env (TupleT ts) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ type_memory_size tv < 2 ** 64 /\
  vyper_to_abi env (TupleT ts) v = SOME av ==>
  has_type (vyper_to_abi_type env (TupleT ts)) av
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >>
  rename1 `ArrayV a` >> Cases_on `a` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, value_has_type_def, val_wf_def,
      evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  drule_all ctor_supported_scalar_list_conversion >> strip_tac >>
  reverse conj_tac
  >- simp[ctor_abi_types_map, has_types_LIST_REL] >>
  drule_all ctor_scalar_list_memory_lower >> strip_tac >>
  drule ctor_tuple_conversion_length >> strip_tac >>
  imp_res_tac vyperTypeABITheory.OPT_MMAP_LENGTH >>
  gvs[type_memory_size_def, wordsTheory.dimword_def] >> decide_tac
QED

Theorem ctor_supported_dynamic_strict_bounded:
  supported_scalar_type ty /\ evaluate_type env (ArrayT ty (Dynamic n)) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ type_memory_size tv < 2 ** 64 /\
  vyper_to_abi env (ArrayT ty (Dynamic n)) v = SOME av ==>
  has_type (vyper_to_abi_type env (ArrayT ty (Dynamic n))) av
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >>
  rename1 `ArrayV a` >> Cases_on `a` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, value_has_type_def, val_wf_def, AllCaseEqs()] >>
  drule_all ctor_scalar_same_alignment >> strip_tac >>
  drule_all ctor_conversion_same_lift >> strip_tac >>
  imp_res_tac ctor_same_conversion_length >>
  drule_all ctor_supported_scalar_memory_lower >> strip_tac >>
  gvs[type_memory_size_def, has_type_def] >>
  `1 <= type_memory_size tv'` by decide_tac >>
  imp_res_tac ctor_bounded_product_offset >>
  simp[wordsTheory.dimword_def, has_types_LIST_REL, LIST_REL_EL_EQN,
       EL_REPLICATE] >> gvs[EVERY_EL]
QED

Theorem ctor_supported_struct_strict_bounded:
  FLOOKUP env id = SOME (StructArgs args) /\
  EVERY supported_scalar_type (MAP SND args) /\
  evaluate_type env (StructT id) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ type_memory_size tv < 2 ** 64 /\
  vyper_to_abi env (StructT id) v = SOME av ==>
  has_type (vyper_to_abi_type env (StructT id)) av
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (imp_res_tac vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  gvs[value_has_type_def, val_wf_def] >>
  drule ctor_scalar_fields_alignment >> simp[] >> strip_tac >>
  drule_all ctor_supported_scalar_list_conversion >> strip_tac >>
  simp[ctor_abi_types_map, has_types_LIST_REL] >>
  drule_all ctor_scalar_list_memory_lower >> strip_tac >>
  drule ctor_tuple_conversion_length >> strip_tac >>
  gvs[type_memory_size_def, ctor_fields_memory_zip, wordsTheory.dimword_def] >> decide_tac
QED

Theorem ctor_scalar_sparse_point_strict:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  sparse_has_type tv n sparse /\ kvs_val_wf sparse tv n /\
  vyper_to_abi_sparse env ty tv n sparse = SOME avs /\ k < n ==>
  has_type (vyper_to_abi_type env ty) (EL k avs)
Proof
  strip_tac >> Cases_on `ALOOKUP sparse k`
  >- (drule_all ctor_canonical_sparse_absent >> simp[] >>
      metis_tac[ctor_supported_scalar_default_strict_type]) >>
  drule_all abiStaticSparsePropsTheory.canonical_sparse_lookup >> strip_tac >>
  drule_all ctor_sparse_scalar_alignment >> simp[EVERY_MEM] >> strip_tac >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  metis_tac[ctor_supported_scalar_strict_type]
QED


Theorem ctor_supported_fixed_strict_bounded:
  supported_scalar_type ty /\ evaluate_type env (ArrayT ty (Fixed n)) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ type_memory_size tv < 2 ** 64 /\
  vyper_to_abi env (ArrayT ty (Fixed n)) v = SOME av ==>
  has_type (vyper_to_abi_type env (ArrayT ty (Fixed n))) av
Proof
  Cases_on `v` >> simp[Once vyper_to_abi_def] >>
  rename1 `ArrayV a` >> Cases_on `a` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, value_has_type_def, val_wf_def, AllCaseEqs()] >>
  imp_res_tac abiStaticSparsePropsTheory.canonical_sparse_length >>
  `!k. k < n ==> has_type (vyper_to_abi_type env ty) (EL k avs)` by
    metis_tac[ctor_scalar_sparse_point_strict] >>
  simp[has_type_def, has_types_LIST_REL, LIST_REL_EL_EQN, EL_REPLICATE] >>
  drule_all ctor_supported_scalar_memory_lower >> strip_tac >>
  `1 <= type_memory_size tv'` by decide_tac >>
  fs[type_memory_size_def] >> imp_res_tac ctor_bounded_product >> decide_tac
QED

Theorem ctor_supported_value_strict_type_bounded:
  supported_value_type tops ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ type_memory_size tv < 2 ** 64 /\
  vyper_to_abi (type_env tops) ty v = SOME av ==>
  has_type (vyper_to_abi_type (type_env tops) ty) av
Proof
  strip_tac >> Cases_on `supported_scalar_type ty`
  >- metis_tac[ctor_supported_scalar_strict_type] >>
  fs[supported_value_type_def] >> Cases_on `ty` >> gvs[AllCaseEqs()]
  >- metis_tac[SRULE [] ctor_supported_tuple_strict_bounded]
  >- (Cases_on `b` >> gvs[] >>
      metis_tac[SRULE [] ctor_supported_fixed_strict_bounded,
        SRULE [] ctor_supported_dynamic_strict_bounded, supported_scalar_type_def]) >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  drule ctor_supported_struct_lookup >> strip_tac >>
  `EVERY supported_scalar_type (MAP SND x)` by
    (gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[supported_scalar_type_def]) >>
  drule_all (SRULE [] ctor_supported_struct_strict_bounded) >> simp[]
QED
