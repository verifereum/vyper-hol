(* Constructor boundaries take semantic child representations, not plans. *)
Theory exprSimAbiEncodeSourceClosure
Ancestors
  exprSimAbiEncodePlanDomain exprSimAbiEncodePlanTranslation
  exprSimAbiEncodePlanMetadata option exprLowering compileEnv
  abiEncoderSourceAggregate abiEncoderSourceWindow abiEncoderProps
  vyperABI contractABI abiDecodeRanges abiEncoderSourcePrimitive abiEncoderInput
  list rich_list valueEncodingProofs vyperValueOperation
  abiEncoderSourceTransport abiEncoderOpenInput vyperValue valueEncoding vyperTyping

Theorem abi_encode_source_tuple:
  source_reps env ts infos cts /\
  is_dynamic (vyper_to_abi_type env (TupleT ts)) ==>
  source_rep env (TupleT ts) (AbiComplex infos) (Tuple cts)
Proof
  rpt strip_tac >>
  drule source_reps_any_dynamic >> strip_tac >>
  drule source_reps_tuple_head >> strip_tac >>
  simp[source_rep_def, vyper_to_abi_type_def] >> rpt strip_tac >>
  `?tvs. tv = TupleTV tvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (ArrayV (TupleV vs)) _ _` >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_tuple_parent >>
  simp[value_has_type_def] >>
  disch_then (qspecl_then [`ts`, `env`, `av`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `!i. i < LENGTH ts ==>
    evaluate_type env (EL i ts) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs) /\
    val_in_memory (EL i tvs) (EL i vs)
      (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem` by simp[] >>
  drule_all source_reps_members >> strip_tac >>
  qexists_tac `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
       enc (Tuple (vyper_to_abi_types env ts)) (ListV avs)` by
        (irule abi_encoder_tuple_encoding_cong >>
         drule source_reps_abi_metadata >> strip_tac >>
         drule source_reps_lengths >> strip_tac >>
         simp[source_translation_list, EL_MAP]) >>
      gvs[Once enc_def]) >>
  irule abi_encoder_source_complex_input >> conj_tac
  >- (`!i. i < LENGTH ts ==>
         evaluate_type env (EL i ts) = SOME (EL i tvs)` by simp[] >>
      drule_all source_reps_full_span >>
      simp[type_memory_size_def, type_memory_size_list_sum]) >>
  qexists_tac `cts` >>
  drule source_reps_lengths >> simp[abi_encoder_tuple_type_def]
QED

Theorem abi_encode_source_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  source_reps (env \\ nsid) (MAP SND args) infos cts /\
  is_dynamic (vyper_to_abi_type env (StructT nsid)) ==>
  source_rep env (StructT nsid) (AbiComplex infos) (Tuple cts)
Proof
  rpt strip_tac >>
  drule source_reps_any_dynamic >> strip_tac >>
  drule source_reps_tuple_head >> strip_tac >>
  simp[source_rep_def, vyper_to_abi_type_def] >> rpt strip_tac >>
  `?ftvs. tv = StructTV ftvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (StructV fields) _ _` >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_struct_parent >>
  simp[value_has_type_def] >>
  disch_then (qspecl_then [`nsid`, `env`, `av`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `!i. i < LENGTH (MAP SND args) ==>
    evaluate_type (env \\ nsid) (EL i (MAP SND args)) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i (MAP SND fields)) /\
    vyper_to_abi (env \\ nsid) (EL i (MAP SND args)) (EL i (MAP SND fields)) = SOME (EL i avs) /\
    val_in_memory (EL i tvs) (EL i (MAP SND fields))
      (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem` by simp[] >>
  `LENGTH tvs = LENGTH (MAP SND args) /\
   LENGTH (MAP SND fields) = LENGTH (MAP SND args) /\
   LENGTH avs = LENGTH (MAP SND args)` by simp[] >>
  drule_all source_reps_members >> strip_tac >>
  qexists_tac `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
       enc (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args))) (ListV avs)` by
        (irule abi_encoder_tuple_encoding_cong >>
         drule source_reps_abi_metadata >> strip_tac >>
         drule source_reps_lengths >> strip_tac >>
         simp[source_translation_list, EL_MAP]) >>
      gvs[Once enc_def]) >>
  irule abi_encoder_source_complex_input >> conj_tac
  >- (`!i. i < LENGTH (MAP SND args) ==>
         evaluate_type (env \\ nsid) (EL i (MAP SND args)) = SOME (EL i tvs)` by simp[] >>
      drule_all source_reps_full_span >>
      simp[type_memory_size_def, type_memory_size_fields_sum, GSYM MAP_MAP_o, MAP_ZIP]) >>
  qexists_tac `cts` >>
  drule source_reps_lengths >> simp[abi_encoder_tuple_type_def]
QED

Theorem abi_encode_source_dynarray:
  evaluate_type env ty = SOME tv /\ source_rep env ty ei ct ==>
  source_rep env (ArrayT ty (Dynamic n))
    (AbiDynArray ei (abi_member_head_size ct) (type_memory_size tv) (is_dynamic ct))
    (Array NONE ct)
Proof
  rpt strip_tac >> drule_all source_rep_metadata >> strip_tac >>
  simp[source_rep_def, vyper_to_abi_type_def, is_dynamic_def, abi_member_head_size_def] >>
  rpt strip_tac >>
  `tv' = ArrayTV tv (Dynamic n)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (ArrayV (DynArrayV vs)) _ _` >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_dynamic_source >>
  simp[value_has_type_def, Once vyper_to_abi_def] >> strip_tac >>
  qpat_x_assum `!t env' av'. _`
    (qspecl_then [`ty`, `env`, `av`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  `!i. i < LENGTH vs ==> ?rv.
    enc ct rv = enc (vyper_to_abi_type env ty) (EL i avs) /\
    abi_encoder_open_input ei ct rv (sb+32+i*type_memory_size tv)
      (type_memory_size tv) mem` by
    (rpt strip_tac >> irule source_rep_transport >> simp[] >>
     qexists_tac `EL i vs` >> simp[arithmeticTheory.ADD_ASSOC]) >>
  qpat_x_assum `!i. _ ==> ?rv. _` mp_tac >>
  CONV_TAC (LAND_CONV (BINDER_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_IMP_THM)))) >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV SKOLEM_THM)) >>
  disch_then (qx_choose_then `f` assume_tac) >>
  qexists_tac `ListV (GENLIST f (LENGTH vs))` >> conj_tac
  >- (`enc (Array NONE ct) (ListV (GENLIST f (LENGTH vs))) =
       enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
        (irule abi_encoder_dynamic_array_encoding_cong >> simp[]) >>
      gvs[Once enc_def]) >>
  irule abiEncoderOpenInputTheory.open_array >> simp[abi_member_head_size_def] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!i. _ ==> enc ct (f i) = _ /\ _`
        (qspec_then `i` mp_tac) >>
      simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC,
        arithmeticTheory.ADD_COMM] >> simp[]) >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >> fs[type_slot_size_def] >>
  `n <= n * type_slot_size tv` by (simp[arithmeticTheory.LE_MULT_LCANCEL]) >>
  decide_tac
QED

Theorem abi_encode_source_sarray:
  source_reps env (REPLICATE n t) infos cts /\
  is_dynamic (vyper_to_abi_type env t) ==>
  ?ct. source_rep env (ArrayT t (Fixed n)) (AbiComplex infos) ct
Proof
  rpt strip_tac >> Cases_on `n = 0`
  >- (gvs[] >> drule source_reps_lengths >> strip_tac >> gvs[] >>
      qexists_tac `Array (SOME 0) (Bytes NONE)` >>
      simp[source_rep_def, vyper_to_abi_type_def, is_dynamic_def,
           abi_member_head_size_def] >> rpt strip_tac >>
      `?tv0. tv = ArrayTV tv0 (Fixed 0)` by
        gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
      gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
      qexists_tac `ListV []` >>
      simp[Once enc_def, abi_encoder_dynamic_empty_input]) >>
  drule source_reps_any_dynamic >> strip_tac >>
  drule source_reps_lengths >> strip_tac >>
  `any_dynamic cts` by
    (fs[source_translation_list, any_dynamic_EXISTS, EXISTS_MEM, MEM_REPLICATE] >>
     metis_tac[]) >>
  qexists_tac `Tuple cts` >>
  simp[source_rep_def, vyper_to_abi_type_def, abi_member_head_size_def,
       is_dynamic_def] >> rpt strip_tac >>
  `?tv0. tv = ArrayTV tv0 (Fixed n)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (ArrayV (SArrayV kvs)) _ _` >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  rename1 `evaluate_type env t = SOME tv` >>
  `tv0 = tv` by gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `value_has_type (ArrayTV tv (Fixed (LENGTH infos))) (ArrayV (SArrayV kvs))` by
    simp[value_has_type_def] >>
  drule_all abi_encoder_sparse_source >> strip_tac >>
  `!i. i < LENGTH (REPLICATE (LENGTH infos) t) ==>
    evaluate_type env (EL i (REPLICATE (LENGTH infos) t)) =
      SOME (EL i (REPLICATE (LENGTH infos) tv)) /\
    value_has_type (EL i (REPLICATE (LENGTH infos) tv))
      (EL i (array_elements (ArrayTV tv (Fixed (LENGTH infos))) (SArrayV kvs))) /\
    vyper_to_abi env (EL i (REPLICATE (LENGTH infos) t))
      (EL i (array_elements (ArrayTV tv (Fixed (LENGTH infos))) (SArrayV kvs))) = SOME (EL i avs) /\
    val_in_memory (EL i (REPLICATE (LENGTH infos) tv))
      (EL i (array_elements (ArrayTV tv (Fixed (LENGTH infos))) (SArrayV kvs)))
      (sb+SUM (MAP type_memory_size (TAKE i (REPLICATE (LENGTH infos) tv)))) mem` by
    (simp[EL_REPLICATE] >> rpt strip_tac >>
     simp[REPLICATE_GENLIST, TAKE_GENLIST] >>
     simp[GSYM REPLICATE_GENLIST, TAKE_GENLIST, arithmeticTheory.MIN_DEF,
          arithmeticTheory.MULT_COMM]) >>
  `LENGTH (REPLICATE (LENGTH infos) tv) = LENGTH (REPLICATE (LENGTH infos) t) /\
   LENGTH (array_elements (ArrayTV tv (Fixed (LENGTH infos))) (SArrayV kvs)) =
     LENGTH (REPLICATE (LENGTH infos) t) /\
   LENGTH avs = LENGTH (REPLICATE (LENGTH infos) t)` by simp[array_elements_def] >>
  drule_all source_reps_members >> strip_tac >>
  qexists_tac `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
       enc (Tuple (vyper_to_abi_types env (REPLICATE (LENGTH infos) t))) (ListV avs)` by
        (irule abi_encoder_tuple_encoding_cong >>
         drule source_reps_abi_metadata >> strip_tac >>
         simp[source_translation_list, EL_MAP, EL_REPLICATE]) >>
      gvs[Once enc_def, source_translation_list]) >>
  irule abi_encoder_source_complex_input >> conj_tac
  >- (`!i. i < LENGTH (REPLICATE (LENGTH infos) t) ==>
         evaluate_type env (EL i (REPLICATE (LENGTH infos) t)) =
           SOME (EL i (REPLICATE (LENGTH infos) tv))` by simp[EL_REPLICATE] >>
      drule_all source_reps_full_span >> simp[type_memory_size_def]) >>
  qexists_tac `cts` >> simp[abi_encoder_tuple_type_def]
QED

Theorem abi_encode_source_reps_map:
  !ts.
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  (!t. MEM t ts ==> IS_SOME (evaluate_type E t) /\
    ?ct. source_rep E t (f t) ct) ==>
  ?cts. source_reps E ts
    (MAP (\t. (f t, abi_embedded_static_size ce.ce_struct_fields t,
      type_memory_bytes ce t, is_abi_dynamic ce.ce_struct_fields t)) ts) cts
Proof
  Induct
  >- (simp[] >> rpt strip_tac >> qexists_tac `[]` >> simp[source_reps_nil]) >>
  rpt strip_tac >>
  `IS_SOME (evaluate_type E h) /\ ?ct. source_rep E h (f h) ct` by
    (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  `?tv. evaluate_type E h = SOME tv` by metis_tac[IS_SOME_EXISTS] >>
  `?cts. source_reps E ts
    (MAP (\t. (f t, abi_embedded_static_size ce.ce_struct_fields t,
      type_memory_bytes ce t, is_abi_dynamic ce.ce_struct_fields t)) ts) cts` by
    (first_x_assum irule >> simp[]) >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  qexists_tac `ct::cts` >> simp[] >> irule source_reps_cons >> simp[] >>
  drule_all source_rep_metadata >> simp[abi_member_head_size_def]
QED

Theorem abi_encode_none_dynarray_source_rep:
  source_rep E (ArrayT NoneT (Dynamic n))
    (type_to_abi_enc_info sf ce (ArrayT NoneT (Dynamic n)))
    (Array NONE (Tuple []))
Proof
  `source_rep E NoneT (AbiComplex []) (Tuple [])` by
    metis_tac[abi_encode_none_source_rep, abi_encode_none_source_domain] >>
  `evaluate_type E NoneT = SOME NoneTV` by simp[] >>
  drule_all abi_encode_source_dynarray >>
  disch_then (qspec_then `n` mp_tac) >>
  simp[type_to_abi_enc_info_def, abi_static_size_def, abi_embedded_static_size_def,
       is_abi_dynamic_def, type_memory_bytes_def, type_memory_size_def,
       abi_member_head_size_def, is_dynamic_def]
QED
