Theory ctorDeployLoweringEntryAggregateInputs
Ancestors
  valueEncodingDefs
 ctorDeployLoweringEntryScalarInputs ctorDeployLoweringEntryQuantitativeInputs supportedTypes vyperABI vyperValue
 vyperTyping vyperTypeValues valueEncoding contractABI list option finite_map
 vyperTypeABI vyperABIRoundtrip abiDecodeRanges ctorDeployLoweringEntrySparseInputs
 retAbiPlanProps

Theorem deploy_supported_scalar_list_conversion:
 !tys vs avs env.
 EVERY supported_scalar_type tys /\
 LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ val_wf tv v) tys vs /\
 vyper_to_abi_list env tys vs = SOME avs ==>
 has_types (vyper_to_abi_types env tys) avs /\
 abi_to_vyper_list env tys avs = SOME vs
Proof
 Induct_on `tys`
 >- (simp[Once vyper_to_abi_def] >> rpt strip_tac >>
     gvs[vyper_to_abi_def, has_type_def, vyper_to_abi_type_def, abi_to_vyper_def])
 >> Cases_on `vs` >>
 simp[Once vyper_to_abi_def, AllCaseEqs()] >> rpt strip_tac >>
 gvs[] >>
 drule_all deploy_supported_scalar_abi_valid >> strip_tac >>
 drule_all deploy_supported_scalar_abi_reverse >> strip_tac >>
 first_x_assum drule_all >> strip_tac >>
 simp[has_type_def, abi_to_vyper_def]
QED

Theorem deploy_typed_list_inputs[local]:
 !tys tvs vs env.
 LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
 values_have_types tvs vs /\ tuple_val_wf vs tvs ==>
 LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ val_wf tv v) tys vs
Proof
 Induct_on `tys` >> Cases_on `tvs` >> Cases_on `vs` >>
 simp[value_has_type_def, val_wf_def] >> rpt strip_tac >>
 first_x_assum drule_all >> strip_tac >> metis_tac[]
QED


Theorem deploy_supported_tuple_conversion:
 !ty env tv v av.
 supported_tuple_type ty /\ evaluate_type env ty = SOME tv /\
 value_has_type tv v /\ val_wf tv v /\
 type_memory_size tv < dimword(:256) /\
 vyper_to_abi env ty v = SOME av ==>
 has_type (vyper_to_abi_type env ty) av /\ abi_to_vyper env ty av = SOME v
Proof
 Cases_on `ty` >> simp[supported_tuple_type_def] >> rpt strip_tac >>
 gvs[evaluate_type_def, AllCaseEqs()] >>
 Cases_on `v` >> gvs[value_has_type_def] >>
 Cases_on `a` >> gvs[value_has_type_def] >>
 gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
 drule evaluate_types_LIST_REL >> strip_tac >>
 `tuple_val_wf l' tvs` by fs[val_wf_def] >>
 drule_all deploy_typed_list_inputs >> strip_tac >>
 drule_all deploy_supported_scalar_list_conversion >> strip_tac >>
 drule_all (SRULE [] deploy_scalar_tuple_strict_cardinality) >> strip_tac >>
 drule vyper_to_abi_list_EL >> strip_tac >>
 gvs[abi_to_vyper_def, LIST_REL_EL_EQN, value_has_type_def]
QED

Theorem deploy_scalar_same_conversion:
 !vs avs ty env tv.
 supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
 all_have_type tv vs /\ EVERY (val_wf tv) vs /\
 vyper_to_abi_same env ty vs = SOME avs ==>
 has_types (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty)) avs /\
 abi_to_vyper_list env (REPLICATE (LENGTH vs) ty) avs = SOME vs
Proof
 Induct_on `vs` >> simp[Once vyper_to_abi_def, value_has_type_def] >>
 rpt strip_tac >> gvs[AllCaseEqs()] >>
 drule_all deploy_supported_scalar_abi_valid >> strip_tac >>
 drule_all deploy_supported_scalar_abi_reverse >> strip_tac >>
 first_x_assum drule_all >> strip_tac >>
 simp[has_type_def, abi_to_vyper_def]
QED

Theorem deploy_elems_val_wf_EVERY[local]:
 !vs tv. elems_val_wf vs tv = EVERY (val_wf tv) vs
Proof
 Induct >> simp[val_wf_def]
QED

Theorem deploy_supported_dynamic_array_conversion:
 !ty n env tv v av.
 supported_word_type ty /\ evaluate_type env (ArrayT ty (Dynamic n)) = SOME tv /\
 value_has_type tv v /\ val_wf tv v /\
 type_memory_size tv < dimword(:256) /\
 vyper_to_abi env (ArrayT ty (Dynamic n)) v = SOME av ==>
 has_type (vyper_to_abi_type env (ArrayT ty (Dynamic n))) av /\
 abi_to_vyper env (ArrayT ty (Dynamic n)) av = SOME v
Proof
 rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
 Cases_on `v` >> gvs[value_has_type_def] >>
 Cases_on `a` >> gvs[value_has_type_def] >>
 gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
 `supported_scalar_type ty` by simp[supported_scalar_type_def] >>
 `EVERY (val_wf tv') l` by gvs[val_wf_def, deploy_elems_val_wf_EVERY] >>
 drule_all deploy_scalar_same_conversion >> strip_tac >>
 `n < dimword(:256)` by
   (irule deploy_word_array_strict_cardinality >>
    qexistsl_tac [`Dynamic n`, `env`, `tv'`, `ty`] >> simp[]) >>
 drule has_types_length >> simp[] >> strip_tac >>
 gvs[abi_to_vyper_def, vyper_to_abi_type_def, has_type_def,
     compatible_bound_def, make_array_value_def]
QED

Theorem deploy_address_default_size[local]:
 dimindex(:160) DIV 8 = 20
Proof
 CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]
QED

Theorem deploy_word_default_inputs[local]:
 !ty env tv. supported_word_type ty /\ evaluate_type env ty = SOME tv ==>
 value_has_type tv (default_value tv) /\ val_wf tv (default_value tv)
Proof
 Cases_on `ty` >> simp[supported_word_type_def] >>
 Cases_on `b` >> simp[supported_word_type_def] >> rpt strip_tac >>
 gvs[evaluate_type_def, default_value_def, value_has_type_def, val_wf_def,
     type_memory_size_def, within_int_bound_def, deploy_address_default_size] >>
 rename1 `BytesT bd` >> Cases_on `bd` >>
 gvs[supported_word_type_def, evaluate_type_def, default_value_def,
     value_has_type_def, val_wf_def, type_memory_size_def, AllCaseEqs()]
QED

Theorem deploy_same_append[local]:
 !xs ys env ty.
 vyper_to_abi_same env ty (xs ++ ys) =
 case vyper_to_abi_same env ty xs of NONE => NONE | SOME avs =>
 case vyper_to_abi_same env ty ys of NONE => NONE | SOME bvs => SOME (avs ++ bvs)
Proof
 Induct >> simp[vyper_to_abi_def] >> rpt gen_tac >>
 Cases_on `vyper_to_abi env ty h` >> simp[] >>
 Cases_on `vyper_to_abi_same env ty xs` >> simp[] >>
 Cases_on `vyper_to_abi_same env ty ys` >> simp[]
QED

Theorem deploy_sparse_dense_conversion:
 !n env ty tv sparse.
 evaluate_type env ty = SOME tv ==>
 vyper_to_abi_same env ty
  (GENLIST (\i. case ALOOKUP sparse i of
                  SOME v => v | NONE => default_value tv) n) =
 vyper_to_abi_sparse env ty tv n sparse
Proof
 Induct >> simp[GENLIST, SNOC_APPEND, deploy_same_append, Once vyper_to_abi_def] >>
 rpt strip_tac >> simp[] >>
 Cases_on `vyper_to_abi_sparse env ty tv n sparse` >> simp[Once vyper_to_abi_def] >>
 Cases_on `ALOOKUP sparse n` >>
 simp[vyper_to_abi_def, vyper_to_abi_default_value] >>
 Cases_on `vyper_to_abi env ty x'` >> simp[]
QED

Theorem deploy_sparse_member_inputs[local]:
 !sparse tv n k v.
 sparse_has_type tv n sparse /\ kvs_val_wf sparse tv n /\ MEM (k,v) sparse ==>
 value_has_type tv v /\ val_wf tv v
Proof
 Induct >> simp[value_has_type_def, val_wf_def] >>
 Cases_on `h` >> simp[value_has_type_def, val_wf_def] >>
 rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem deploy_sparse_selected_inputs[local]:
 !ty env tv n sparse i.
 supported_word_type ty /\ evaluate_type env ty = SOME tv /\
 sparse_has_type tv n sparse /\ kvs_val_wf sparse tv n ==>
 value_has_type tv (case ALOOKUP sparse i of SOME v => v | NONE => default_value tv) /\
 val_wf tv (case ALOOKUP sparse i of SOME v => v | NONE => default_value tv)
Proof
 rpt gen_tac >> strip_tac >> Cases_on `ALOOKUP sparse i`
 >- (drule_all deploy_word_default_inputs >> simp[]) >>
 drule alistTheory.ALOOKUP_MEM >> strip_tac >>
 drule_all deploy_sparse_member_inputs >> simp[]
QED

Theorem deploy_sparse_scalar_conversion:
 !ty env tv n sparse avs.
 supported_word_type ty /\ evaluate_type env ty = SOME tv /\
 sparse_has_type tv n sparse /\
 val_wf (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) /\
 vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
 LENGTH avs = n /\
 has_types (REPLICATE n (vyper_to_abi_type env ty)) avs /\
 abi_to_vyper_list env (REPLICATE n ty) avs =
  SOME (GENLIST (\i. case ALOOKUP sparse i of
                      SOME v => v | NONE => default_value tv) n)
Proof
 rpt gen_tac >> strip_tac >>
 `kvs_val_wf sparse tv n` by gvs[val_wf_def] >>
 `supported_scalar_type ty` by simp[supported_scalar_type_def] >>
 qmatch_goalsub_abbrev_tac `SOME dense` >>
 `all_have_type tv dense /\ EVERY (val_wf tv) dense` by
   (simp[Abbr `dense`, all_have_type_EVERY, EVERY_GENLIST] >>
    rpt strip_tac >> drule_all deploy_sparse_selected_inputs >> simp[]) >>
 `vyper_to_abi_same env ty dense = SOME avs` by
   simp[Abbr `dense`, deploy_sparse_dense_conversion] >>
 drule_all deploy_scalar_same_conversion >> strip_tac >>
 drule has_types_length >> simp[Abbr `dense`] >> strip_tac >>
 gvs[]
QED

Theorem deploy_supported_fixed_array_conversion:
 !ty n env tv v av.
 supported_word_type ty /\ evaluate_type env (ArrayT ty (Fixed n)) = SOME tv /\
 value_has_type tv v /\ val_wf tv v /\
 type_memory_size tv < dimword(:256) /\
 vyper_to_abi env (ArrayT ty (Fixed n)) v = SOME av ==>
 has_type (vyper_to_abi_type env (ArrayT ty (Fixed n))) av /\
 abi_to_vyper env (ArrayT ty (Fixed n)) av = SOME v
Proof
 rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
 Cases_on `v` >> gvs[value_has_type_def] >>
 Cases_on `a` >> gvs[value_has_type_def] >>
 gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
 drule_all deploy_sparse_scalar_conversion >> strip_tac >>
 `n < dimword(:256)` by
   (irule deploy_word_array_strict_cardinality >>
    qexistsl_tac [`Fixed n`, `env`, `tv'`, `ty`] >> simp[]) >>
 drule_all deploy_typed_sparse_reconstruction >> strip_tac >>
 gvs[abi_to_vyper_def, vyper_to_abi_type_def, has_type_def,
     compatible_bound_def, make_array_value_def]
QED

Theorem deploy_supported_struct_lookup:
 !tops id fields.
 supported_struct_fields tops id = SOME fields ==>
 FLOOKUP (type_env tops) id = SOME (StructArgs fields)
Proof
 metis_tac[supported_struct_fields_type_env]
QED

Theorem deploy_struct_fields_tuple_wf[local]:
 !fs fts. fields_val_wf fs fts ==>
 tuple_val_wf (MAP SND fs) (MAP SND fts)
Proof
 Induct >> Cases_on `fts` >> simp[val_wf_def] >>
 rpt gen_tac >> PairCases_on `h` >> simp[val_wf_def] >>
 PairCases_on `h'` >> simp[val_wf_def]
QED

Theorem deploy_struct_memory_size_values[local]:
 !fts. type_memory_size_fields fts = type_memory_size_list (MAP SND fts)
Proof
 Induct >> simp[type_memory_size_def] >> Cases_on `h` >> simp[type_memory_size_def]
QED

Theorem deploy_supported_struct_conversion:
 !env id fields tv v av.
 FLOOKUP env id = SOME (StructArgs fields) /\
 EVERY (supported_word_type o SND) fields /\
 evaluate_type env (StructT id) = SOME tv /\
 value_has_type tv v /\ val_wf tv v /\
 type_memory_size tv < dimword(:256) /\
 vyper_to_abi env (StructT id) v = SOME av ==>
 has_type (vyper_to_abi_type env (StructT id)) av /\
 abi_to_vyper env (StructT id) av = SOME v
Proof
 rpt gen_tac >> strip_tac >>
 gvs[evaluate_type_def, AllCaseEqs()] >>
 Cases_on `v` >> gvs[value_has_type_def] >>
 gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
 drule evaluate_types_LIST_REL >> strip_tac >>
 drule struct_has_type_map_fst >> strip_tac >>
 drule struct_has_type_values_have_types >> strip_tac >>
 `LENGTH fields = LENGTH tvs` by fs[LIST_REL_EL_EQN] >>
 gvs[MAP_ZIP] >>
 `tuple_val_wf (MAP SND l) tvs` by
   (fs[val_wf_def] >> drule deploy_struct_fields_tuple_wf >> simp[MAP_ZIP]) >>
 `EVERY supported_scalar_type (MAP SND fields)` by
   gvs[EVERY_MAP, EVERY_MEM, supported_scalar_type_def] >>
 drule_all deploy_typed_list_inputs >> strip_tac >>
 drule_all deploy_supported_scalar_list_conversion >> strip_tac >>
 `type_memory_size (TupleTV tvs) < dimword(:256)` by
   gvs[type_memory_size_def, deploy_struct_memory_size_values, MAP_ZIP] >>
 drule_all deploy_scalar_tuple_strict_cardinality >> strip_tac >>
 drule has_types_length >> simp[] >> strip_tac >>
 drule vyper_to_abi_list_EL >> strip_tac >> gvs[] >>
 metis_tac[GSYM listTheory.UNZIP_MAP, listTheory.ZIP_UNZIP]
QED

Theorem deploy_supported_value_conversion:
 !tops ty tv v av.
 supported_value_type tops ty /\
 evaluate_type (type_env tops) ty = SOME tv /\
 value_has_type tv v /\ val_wf tv v /\
 type_memory_size tv < dimword(:256) /\
 vyper_to_abi (type_env tops) ty v = SOME av ==>
 has_type (vyper_to_abi_type (type_env tops) ty) av /\
 abi_to_vyper (type_env tops) ty av = SOME v
Proof
 rpt gen_tac >> strip_tac >> Cases_on `supported_scalar_type ty`
 >- metis_tac[deploy_supported_scalar_abi_valid, deploy_supported_scalar_abi_reverse] >>
 Cases_on `ty` >> gvs[supported_value_type_def]
 >- (`supported_tuple_type (TupleT l)` by simp[supported_tuple_type_def] >>
     drule_all (SRULE [] deploy_supported_tuple_conversion) >> simp[])
 >- (rename1 `ArrayT elem bd` >> Cases_on `bd` >> gvs[] >>
     metis_tac[SRULE [] deploy_supported_fixed_array_conversion,
               SRULE [] deploy_supported_dynamic_array_conversion])
 >> Cases_on `supported_struct_fields tops p` >> gvs[] >>
 drule deploy_supported_struct_lookup >> strip_tac >>
 drule_all (SRULE [] deploy_supported_struct_conversion) >> simp[]
QED

Theorem deploy_supported_value_list_conversion:
 !tops tys vals avs.
 EVERY (supported_value_type tops) tys /\
 LIST_REL (\ty v. ?tv.
   evaluate_type (type_env tops) ty = SOME tv /\
   value_has_type tv v /\ val_wf tv v /\
   type_memory_size tv < dimword(:256)) tys vals /\
 vyper_to_abi_list (type_env tops) tys vals = SOME avs ==>
 has_types (vyper_to_abi_types (type_env tops) tys) avs /\
 abi_to_vyper_list (type_env tops) tys avs = SOME vals
Proof
 gen_tac >> Induct_on `tys`
 >- (simp[Once vyper_to_abi_def] >> rpt strip_tac >>
     gvs[vyper_to_abi_def, has_type_def, vyper_to_abi_type_def, abi_to_vyper_def]) >>
 Cases_on `vals` >> simp[Once vyper_to_abi_def, AllCaseEqs()] >>
 rpt strip_tac >> gvs[] >>
 drule_all (SRULE [] deploy_supported_value_conversion) >> strip_tac >>
 first_x_assum drule_all >> strip_tac >>
 simp[has_type_def, abi_to_vyper_def]
QED
