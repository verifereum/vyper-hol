(* Semantic translation includes zero-byte children, independently of plans. *)
Theory exprSimAbiEncodeSourceTranslation
Ancestors
  exprSimAbiEncodeSourceClosure exprSimAbiEncodePlanDomain
  exprSimAbiEncodePlanTranslation exprSimAbiEncodePlanMetadata
  abiEncoderSourceAggregate abiEncoderSourceProducer abiEncoderProps
  abiEncoderOpenInput abiEncoderInput exprLowering compileEnv retAbiPlanProps abiTypeBoundProps
  abiDecodeRanges contractABI finite_map list rich_list option vyperTypeSystem vyperValue vyperABI pair combin

Theorem abi_encode_source_map_fields[local]:
  !fields. MAP (\(fn, fty, sz). g fty) fields = MAP g (MAP (FST o SND) fields)
Proof
  Induct >> simp[FORALL_PROD]
QED

Theorem abi_encode_source_static_copy[local]:
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  evaluate_type E ty = SOME tv /\ ~is_abi_dynamic ce.ce_struct_fields ty ==>
  ?ct. source_rep E ty (AbiCopy (type_memory_bytes ce ty)) ct
Proof
  strip_tac >> drule_all abi_encode_element_metadata >> strip_tac >> gvs[] >>
  irule source_rep_static_copy >> simp[]
QED

Theorem abi_encode_source_array[local]:
  evaluate_type E (ArrayT elem bd) = SOME tv /\
  evaluate_type E elem = SOME etv /\
  source_rep E elem (type_to_abi_enc_info sf ce elem) ect /\
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) ==>
  ?ct. source_rep E (ArrayT elem bd) (type_to_abi_enc_info sf ce (ArrayT elem bd)) ct
Proof
  strip_tac >> Cases_on `bd` >> simp[Once type_to_abi_enc_info_def]
  >- (IF_CASES_TAC >- (drule_all abi_encode_source_static_copy >> simp[]) >>
      simp[GSYM REPLICATE_GENLIST] >>
      `?cts. source_reps E (REPLICATE n elem)
        (MAP (\t. (type_to_abi_enc_info sf ce t,
          abi_embedded_static_size ce.ce_struct_fields t, type_memory_bytes ce t,
          is_abi_dynamic ce.ce_struct_fields t)) (REPLICATE n elem)) cts` by
        (irule abi_encode_source_reps_map >> simp[MEM_REPLICATE] >>
         conj_tac >- metis_tac[] >> qexists `E0` >> simp[]) >>
      drule_all abi_encode_element_metadata >> strip_tac >>
      `is_dynamic (vyper_to_abi_type E elem)` by gvs[is_abi_dynamic_def] >>
      drule_all abi_encode_source_sarray >> gvs[]) >>
  qpat_x_assum `evaluate_type E elem = _` assume_tac >>
  drule_all abi_encode_element_metadata >> strip_tac >> simp[] >>
  drule_all source_rep_metadata >> strip_tac >>
  drule_all abi_encode_source_dynarray >>
  disch_then (qspec_then `n` mp_tac) >>
  simp[abi_member_head_size_def] >> strip_tac >> qexists `Array NONE ect` >> simp[]
QED

Theorem abi_encode_source_rep_upto:
  !tv E ty sf ce E0.
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  abi_sfields_consistent_upto (type_value_size tv) sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) ==>
  ?ct. source_rep E ty (type_to_abi_enc_info sf ce ty) ct
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  Cases_on `ty`
  >~ [`BaseT b`] >- suspend "base"
  >~ [`ArrayT elem bd`] >- suspend "array"
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`StructT k`] >- suspend "struct"
  >~ [`FlagT k`] >- suspend "flag"
  >~ [`NoneT`] >- metis_tac[abi_encode_none_source_rep]
  >> gvs[Once evaluate_type_def]
QED

Resume abi_encode_source_rep_upto[base]:
  `abi_enc_plan E (BaseT b) (type_to_abi_enc_info sf ce (BaseT b))` by
    (Cases_on `b` >>
     simp[type_to_abi_enc_info_def, abi_enc_plan_bytes, abi_enc_plan_string]
     >~ [`BytesT bd`] >- (Cases_on `bd` >>
       simp[type_to_abi_enc_info_def, abi_enc_plan_bytes] >>
       irule abi_encode_plan_static_copy >> simp[is_abi_dynamic_def] >>
       first_assum (irule_at Any) >> simp[]) >>
     irule abi_encode_plan_static_copy >> simp[is_abi_dynamic_def] >>
     first_assum (irule_at Any) >> simp[]) >>
  metis_tac[abi_encoder_uniform_source]
QED
Resume abi_encode_source_rep_upto[array]:
  drule evaluate_type_array_child_size >> strip_tac >>
  `abi_sfields_consistent_upto (type_value_size u) sf E` by
    (irule abi_sfields_consistent_upto_mono >>
     qexists `type_value_size tv` >> simp[]) >>
  `?ect. source_rep E elem (type_to_abi_enc_info sf ce elem) ect` by
    (first_x_assum drule >> disch_then irule >> simp[] >>
     qexists `E0` >> simp[]) >>
  drule_all abi_encode_source_array >> simp[]
QED
Resume abi_encode_source_rep_upto[tuple]:
  simp[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC >- (drule_all abi_encode_source_static_copy >> simp[]) >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  `?cts. source_reps E ts
    (MAP (\t. (type_to_abi_enc_info sf ce t,
      abi_embedded_static_size ce.ce_struct_fields t, type_memory_bytes ce t,
      is_abi_dynamic ce.ce_struct_fields t)) ts) cts` by
    (irule abi_encode_source_reps_map >> simp[] >>
     reverse conj_tac >- (qexists `E0` >> simp[]) >>
     gen_tac >> strip_tac >>
     `?u. evaluate_type E t = SOME u /\ type_value_size u < type_value_size tv` by
       metis_tac[evaluate_type_tuple_child_size] >>
     `abi_sfields_consistent_upto (type_value_size u) sf E` by
       (irule abi_sfields_consistent_upto_mono >>
        qexists `type_value_size tv` >> simp[]) >>
     conj_tac >- simp[] >>
     first_x_assum drule >> disch_then irule >> simp[] >>
     qexists `E0` >> simp[]) >>
  `is_dynamic (vyper_to_abi_type E (TupleT ts))` by gvs[] >>
  drule_all abi_encode_source_tuple >> metis_tac[]
QED
Resume abi_encode_source_rep_upto[struct]:
  `?args. FLOOKUP E k = SOME (StructArgs args)` by
    (qpat_x_assum `evaluate_type E (StructT k) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  drule abi_sfields_consistent_upto_lookup >>
  disch_then drule >> disch_then drule >> simp[] >> strip_tac >>
  simp[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC >- (drule_all abi_encode_source_static_copy >> simp[]) >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  simp[abi_encode_source_map_fields] >>
  `?cts. source_reps (E \\ k) (MAP SND args)
    (MAP (\t. (type_to_abi_enc_info (sf \\ nsid_to_string k) ce t,
      abi_embedded_static_size ce.ce_struct_fields t, type_memory_bytes ce t,
      is_abi_dynamic ce.ce_struct_fields t)) (MAP SND args)) cts` by
    (irule abi_encode_source_reps_map >> simp[] >>
     reverse conj_tac
     >- (qexists `E0` >> simp[] >> irule SUBMAP_TRANS >> qexists `E` >> simp[]) >>
     gen_tac >> strip_tac >>
     `?u. evaluate_type (E \\ k) t = SOME u /\ type_value_size u < type_value_size tv` by
       metis_tac[evaluate_type_struct_child_size] >>
     `abi_sfields_consistent_upto (type_value_size u) (sf \\ nsid_to_string k) (E \\ k)` by
       (irule abi_sfields_consistent_upto_domsub >>
        simp[] >> qexists `type_value_size tv` >> simp[]) >>
     conj_tac >- simp[] >>
     first_x_assum drule >> disch_then irule >> simp[] >>
     qexists `E0` >> simp[] >> irule SUBMAP_TRANS >> qexists `E` >> simp[]) >>
  `is_dynamic (vyper_to_abi_type E (StructT k))` by gvs[] >>
  drule_all abi_encode_source_struct >> metis_tac[]
QED
Resume abi_encode_source_rep_upto[flag]:
  simp[type_to_abi_enc_info_def] >>
  irule abi_encode_source_static_copy >> simp[is_abi_dynamic_def] >>
  first_assum (irule_at Any) >> simp[]
QED
Finalise abi_encode_source_rep_upto

Theorem abi_encode_translated_source_rep:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) ==>
  ?ct. source_rep E ty (type_to_abi_enc_info sf ce ty) ct
Proof
  strip_tac >> irule abi_encode_source_rep_upto >> simp[] >>
  conj_tac >- (qexists `E0` >> simp[]) >>
  irule abi_sfields_consistent_upto_init >> simp[]
QED

Theorem abi_encode_translated_source_window:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  value_has_type tv v /\ vyper_to_abi E ty v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?ct rv. source_rep E ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type E ty) av /\
    abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv sb (type_memory_size tv) mem
Proof
  strip_tac >> drule_all abi_encode_translated_source_rep >> strip_tac >>
  drule_all source_rep_transport >> strip_tac >>
  qexistsl_tac [`ct`, `rv`] >> simp[]
QED

Theorem abi_encode_nested_none_source_rep:
  evaluate_type E (TupleT [NoneT; BaseT (BytesT (Dynamic n))]) = SOME tv /\
  sfields_tenv_consistent sf E /\ sfields_tenv_consistent ce.ce_struct_fields E /\
  (!t v. evaluate_type E t = SOME v ==> type_memory_bytes ce t = type_memory_size v) ==>
  ?ct. source_rep E (TupleT [NoneT; BaseT (BytesT (Dynamic n))])
    (type_to_abi_enc_info sf ce (TupleT [NoneT; BaseT (BytesT (Dynamic n))])) ct
Proof
  strip_tac >> irule abi_encode_translated_source_rep >> simp[] >>
  qexists `E` >> simp[]
QED
