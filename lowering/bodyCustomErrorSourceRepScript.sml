Theory bodyCustomErrorSourceRep
Ancestors
  abiEncoderSourceProducer abiEncoderSourceAggregate abiEncoderSourcePrimitive
  retAbiPlanProps abiEmptyDispatch loweringStateRelDefs abiEncoderSourceTransport abiEncoderOpenInput abiEncoderInput
  vyperABI vyperValue vyperTyping contractABI list rich_list valueEncoding
  valueEncodingProofs abiEncoderSourceWindow abiEncoderProps abiDecodeRanges
  vyperValueOperation structFieldsProps exprLowering compileEnv finite_map option vyperAST

Theorem custom_error_tuple_source_rep:
  source_reps env ts infos cts ==>
  source_rep env (TupleT ts) (AbiComplex infos) (Tuple cts)
Proof
  strip_tac >>
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

Theorem custom_error_struct_source_rep:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  source_reps (env \\ nsid) (MAP SND args) infos cts ==>
  source_rep env (StructT nsid) (AbiComplex infos) (Tuple cts)
Proof
  strip_tac >>
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

Theorem custom_error_dynamic_array_source_rep:
  evaluate_type env ty = SOME tv /\ source_rep env ty ei ct ==>
  source_rep env (ArrayT ty (Dynamic n))
    (AbiDynArray ei (abi_member_head_size ct) (type_memory_size tv)
      (is_dynamic ct)) (Array NONE ct)
Proof
  strip_tac >> drule_all source_rep_metadata >> strip_tac >>
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
  irule abiEncoderOpenInputTheory.open_array >>
  simp[abi_member_head_size_def] >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!i. _ ==> enc ct (f i) = _ /\ _`
        (qspec_then `i` mp_tac) >>
      simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC,
        arithmeticTheory.ADD_COMM] >> simp[]) >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  fs[type_slot_size_def] >>
  `n <= n * type_slot_size tv` by
    simp[arithmeticTheory.LE_MULT_LCANCEL] >> decide_tac
QED

Theorem custom_error_fixed_array_source_rep:
  evaluate_type env t = SOME tv /\ is_dynamic (vyper_to_abi_type env t) /\
  0 < n /\ source_reps env (REPLICATE n t) infos cts ==>
  source_rep env (ArrayT t (Fixed n)) (AbiComplex infos) (Tuple cts)
Proof
  strip_tac >> drule source_reps_any_dynamic >> strip_tac >>
  drule source_reps_lengths >> strip_tac >>
  `any_dynamic cts` by
    (fs[source_translation_list, any_dynamic_EXISTS, EXISTS_MEM, MEM_REPLICATE] >>
     metis_tac[]) >>
  simp[source_rep_def, vyper_to_abi_type_def, abi_member_head_size_def,
       is_dynamic_def] >> rpt strip_tac >>
  `?tv0. tv' = ArrayTV tv0 (Fixed n)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (ArrayV (SArrayV kvs)) _ _` >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
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
     simp[GSYM REPLICATE_GENLIST, arithmeticTheory.MIN_DEF, arithmeticTheory.MULT_COMM]) >>
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
  >- (drule_at (Pat `source_reps _ _ _ _`) source_reps_full_span >>
      disch_then (qspec_then `REPLICATE (LENGTH infos) tv` mp_tac) >>
      simp[EL_REPLICATE, type_memory_size_def]) >>
  qexists_tac `cts` >> simp[abi_encoder_tuple_type_def]
QED

Theorem custom_error_source_reps_map:
  !ts.
    tenv SUBMAP tenv0 /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
    (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
    (!t tv. evaluate_type tenv0 t = SOME tv ==>
      type_memory_bytes cenv t = type_memory_size tv) /\
    (!t. MEM t ts ==> IS_SOME (evaluate_type tenv t) /\
      ?ct. source_rep tenv t (f t) ct) ==>
    ?cts. source_reps tenv ts
      (MAP (\t. (f t, abi_embedded_static_size cenv.ce_struct_fields t,
        type_memory_bytes cenv t, is_abi_dynamic cenv.ce_struct_fields t)) ts) cts
Proof
  Induct
  >- (rpt strip_tac >> qexists_tac `[]` >> simp[source_reps_nil]) >>
  rpt strip_tac >>
  `?tv. evaluate_type tenv h = SOME tv` by
    metis_tac[IS_SOME_EXISTS, MEM] >>
  `?ct. source_rep tenv h (f h) ct` by metis_tac[MEM] >>
  `?cts. source_reps tenv ts
    (MAP (\t. (f t, abi_embedded_static_size cenv.ce_struct_fields t,
      type_memory_bytes cenv t, is_abi_dynamic cenv.ce_struct_fields t)) ts) cts` by
    (first_x_assum irule >> simp[]) >>
  drule_all abi_elem_props >> strip_tac >>
  drule_all source_rep_metadata >> strip_tac >>
  qexists_tac `ct::cts` >> simp_tac (srw_ss()) [MAP] >> irule source_reps_cons >>
  simp[abi_member_head_size_def]
QED

Theorem custom_error_source_rep_static_translation:
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
    type_memory_bytes cenv t = type_memory_size tv) /\
  evaluate_type tenv ty = SOME tv /\
  ~is_abi_dynamic cenv.ce_struct_fields ty ==>
  ?ct. source_rep tenv ty (AbiCopy (type_memory_bytes cenv ty)) ct
Proof
  strip_tac >> drule_all abi_elem_props >> strip_tac >> gvs[] >>
  irule source_rep_static_copy >> simp[]
QED

Theorem custom_error_evaluated_source_rep_mutual:
  (!tenv ty tv. evaluate_type tenv ty = SOME tv ==>
    !(sf : (string, (string # type # num) list) fmap) cenv tenv0.
      tenv SUBMAP tenv0 /\ sfields_tenv_consistent sf tenv /\
      (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
      sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
      (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
      (!t tv. evaluate_type tenv0 t = SOME tv ==>
        type_memory_bytes cenv t = type_memory_size tv) ==>
      ?ct. source_rep tenv ty (type_to_abi_enc_info sf cenv ty) ct) /\
  (!tenv ts acc tvs. evaluate_types tenv ts acc = SOME tvs ==>
    !(sf : (string, (string # type # num) list) fmap) cenv tenv0.
      tenv SUBMAP tenv0 /\ sfields_tenv_consistent sf tenv /\
      (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
      sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
      (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
      (!t tv. evaluate_type tenv0 t = SOME tv ==>
        type_memory_bytes cenv t = type_memory_size tv) ==>
      !t. MEM t ts ==> IS_SOME (evaluate_type tenv t) /\
        ?ct. source_rep tenv t (type_to_abi_enc_info sf cenv t) ct)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`BaseT bt`]
  >- (rpt strip_tac >> Cases_on `bt` >>
      simp[type_to_abi_enc_info_def]
      >~ [`BytesT bd`] >- (Cases_on `bd` >> simp[type_to_abi_enc_info_def]
        >- (irule custom_error_source_rep_static_translation >>
            simp[is_abi_dynamic_def] >> metis_tac[]) >>
        metis_tac[cj 1 abi_encoder_uniform_source, abi_enc_plan_bytes])
      >~ [`StringT n`] >- metis_tac[cj 1 abi_encoder_uniform_source, abi_enc_plan_string] >>
      irule custom_error_source_rep_static_translation >>
      simp[is_abi_dynamic_def] >> metis_tac[])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> simp[type_to_abi_enc_info_def] >>
      irule custom_error_source_rep_static_translation >>
      simp[is_abi_dynamic_def] >> metis_tac[])
  >~ [`NoneT`]
  >- (rpt strip_tac >> qexists_tac `Tuple []` >>
      simp[type_to_abi_enc_info_def, source_rep_def, vyper_to_abi_type_def,
           evaluate_type_def, value_has_type_def] >>
      rpt strip_tac >> gvs[vyper_to_abi_def] >>
      qexists_tac `ListV []` >> simp[abi_encoder_open_complex_nil])
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`ArrayT ty bd`] >- suspend "array"
  >~ [`StructT nsid`] >- suspend "struct"
  >~ [`evaluate_types tenv [] acc`] >- simp[]
  >> suspend "cons"
QED

Resume custom_error_evaluated_source_rep_mutual[tuple]:
  rpt strip_tac >> simp[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC
  >- (irule custom_error_source_rep_static_translation >> metis_tac[]) >>
  `?tvs. evaluate_types tenv ts [] = SOME tvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `!tvs. _` drule >> strip_tac >>
  `!t. MEM t ts ==> IS_SOME (evaluate_type tenv t) /\
    ?ct. source_rep tenv t (type_to_abi_enc_info sf cenv t) ct` by
    (gen_tac >> disch_tac >>
     first_x_assum (qspecl_then [`sf`, `cenv`, `tenv0`, `t`] mp_tac) >> simp[]) >>
  drule_all custom_error_source_reps_map >>
  disch_then (qx_choose_then `cts` assume_tac) >>
  qexists_tac `Tuple cts` >> irule custom_error_tuple_source_rep >> simp[]
QED

Resume custom_error_evaluated_source_rep_mutual[array]:
  rpt strip_tac >>
  `?etv. evaluate_type tenv ty = SOME etv` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `?ct. source_rep tenv ty (type_to_abi_enc_info sf cenv ty) ct` by
    (first_x_assum drule >> disch_then irule >> simp[] >> metis_tac[]) >>
  drule_all abi_elem_props >> strip_tac >>
  drule_all source_rep_metadata >> strip_tac >>
  Cases_on `bd` >> simp[Once type_to_abi_enc_info_def]
  >- (IF_CASES_TAC
      >- (irule custom_error_source_rep_static_translation >> metis_tac[]) >>
      `?cts. source_reps tenv (REPLICATE n ty)
        (MAP (\t. (type_to_abi_enc_info sf cenv t,
          abi_embedded_static_size cenv.ce_struct_fields t,
          type_memory_bytes cenv t, is_abi_dynamic cenv.ce_struct_fields t))
          (REPLICATE n ty)) cts` by
        (irule custom_error_source_reps_map >> simp[MEM_REPLICATE] >>
         metis_tac[]) >>
      qexists_tac `Tuple cts` >> irule custom_error_fixed_array_source_rep >>
      gvs[is_abi_dynamic_def, GSYM REPLICATE_GENLIST] >>
      gvs[evaluate_type_def, AllCaseEqs(), bound_length_def]) >>
  qexists_tac `Array NONE ct` >>
  drule_all custom_error_dynamic_array_source_rep >>
  disch_then (qspec_then `n` mp_tac) >>
  simp[abi_member_head_size_def]
QED

Resume custom_error_evaluated_source_rep_mutual[struct]:
  rpt strip_tac >>
  `?args tvs. FLOOKUP tenv nsid = SOME (StructArgs args) /\
    evaluate_types (tenv \\ nsid) (MAP SND args) [] = SOME tvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  reverse (Cases_on `is_abi_dynamic cenv.ce_struct_fields (StructT nsid)`)
  >- (simp[Once type_to_abi_enc_info_def] >>
      irule custom_error_source_rep_static_translation >> metis_tac[]) >>
  `?fields. FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `sfields_tenv_consistent sf tenv` mp_tac >>
     simp[sfields_tenv_consistent_def] >> strip_tac >>
     first_x_assum drule >> strip_tac >> simp[]) >>
  drule_all sfields_tenv_consistent_domsub >> strip_tac >>
  `tenv \\ nsid SUBMAP tenv0` by
    (irule SUBMAP_TRANS >> qexists_tac `tenv` >> simp[]) >>
  `!t. MEM t (MAP SND args) ==> IS_SOME (evaluate_type (tenv \\ nsid) t) /\
    ?ct. source_rep (tenv \\ nsid) t
      (type_to_abi_enc_info (sf \\ nsid_to_string nsid) cenv t) ct` by
    (qpat_x_assum `!ty args names. _` drule >> simp[] >>
     disch_then drule >> disch_then (qspecl_then
       [`sf \\ nsid_to_string nsid`, `cenv`] mp_tac) >> simp[]) >>
  drule_all abi_empty_struct_descriptor >> disch_then SUBST1_TAC >> simp[] >>
  `?cts. source_reps (tenv \\ nsid) (MAP SND args)
    (MAP (\t. (type_to_abi_enc_info (sf \\ nsid_to_string nsid) cenv t,
      abi_embedded_static_size cenv.ce_struct_fields t,
      type_memory_bytes cenv t, is_abi_dynamic cenv.ce_struct_fields t))
      (MAP SND args)) cts` by
    (irule custom_error_source_reps_map >> simp[] >> metis_tac[]) >>
  qexists_tac `Tuple cts` >> irule custom_error_struct_source_rep >> simp[]
QED

Resume custom_error_evaluated_source_rep_mutual[cons]:
  rpt strip_tac >>
  `?tv. evaluate_type tenv ty = SOME tv /\
    evaluate_types tenv ts (tv::acc) = SOME tvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[MEM] >> metis_tac[]
QED

Finalise custom_error_evaluated_source_rep_mutual


Theorem custom_error_evaluated_source_rep:
  evaluate_type tenv ty = SOME tv /\
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap) tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
    type_memory_bytes cenv t = type_memory_size tv) ==>
  ?ct. source_rep tenv ty (type_to_abi_enc_info sf cenv ty) ct
Proof
  strip_tac >> drule (cj 1 custom_error_evaluated_source_rep_mutual) >>
  disch_then irule >> simp[] >> metis_tac[]
QED
