Theory abiEncodeTranslatedUniformSource
Ancestors
  exprSimAbiEncodeSourceTranslation exprSimAbiEncodeSourceClosure
  exprSimAbiEncodePlanDomain exprSimAbiEncodePlanMetadata exprSimAbiEncodePlanTranslation
  abiEncoderUniformValueSource abiEncoderUniformArrayConstructor
  abiEncoderUniformAggregateConstructors abiEncoderUniformStaticSource
  abiEncoderSourceAggregate abiEncoderProps abiEncoderOpenInput
  exprLowering compileEnv retAbiPlanProps abiTypeBoundProps abiDecodeRanges
  contractABI finite_map list rich_list option vyperTypeSystem vyperValue vyperABI pair combin abiCallerTupleLayout

Theorem abi_encode_translated_uniform_static[local]:
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  evaluate_type E ty = SOME tv /\ ~is_abi_dynamic ce.ce_struct_fields ty ==>
  ?ct.
    (!u. evaluate_type E ty = SOME u ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E ty)) /\
    (!u v av sb mem0.
      evaluate_type E ty = SOME u /\ value_has_type u v /\
      vyper_to_abi E ty v = SOME av /\ val_in_memory u v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
        !mem. val_in_memory u v sb mem ==>
          abi_encoder_open_input (AbiCopy (type_memory_bytes ce ty)) ct rv sb (type_memory_size u) mem)
Proof
  strip_tac >> drule_all abi_encode_element_metadata >> strip_tac >> gvs[] >>
  drule_all abi_encoder_uniform_static_value_source >> strip_tac >>
  drule_all abi_caller_static_memory >> strip_tac >>
  qexists `ct` >> simp[abi_member_head_size_def] >> metis_tac[]
QED

Theorem abi_encode_translated_uniform_members[local]:
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  (!t. MEM t ts ==> IS_SOME (evaluate_type E t) /\ ?ct.
    (!u. evaluate_type E t = SOME u ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E t) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E t)) /\
    (!u v av sb mem0.
      evaluate_type E t = SOME u /\ value_has_type u v /\
      vyper_to_abi E t v = SOME av /\ val_in_memory u v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E t) av /\
        !mem. val_in_memory u v sb mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce t) ct rv sb (type_memory_size u) mem)) ==>
  ?cts. LENGTH ts = LENGTH cts /\
    !i ei abi_sz mem_sz dyn.
      i < LENGTH ts /\
      EL i (MAP (\t. (type_to_abi_enc_info sf ce t,
        abi_embedded_static_size ce.ce_struct_fields t, type_memory_bytes ce t,
        is_abi_dynamic ce.ce_struct_fields t)) ts) = (ei,abi_sz,mem_sz,dyn) ==>
      ((!u. evaluate_type E (EL i ts) = SOME u ==>
        is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type E (EL i ts)) /\
        abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type E (EL i ts))) /\
       (!u v av sb mem0.
        evaluate_type E (EL i ts) = SOME u /\ value_has_type u v /\
        vyper_to_abi E (EL i ts) v = SOME av /\ val_in_memory u v sb mem0 ==>
        ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type E (EL i ts)) av /\
          !mem. val_in_memory u v sb mem ==>
            abi_encoder_open_input ei (EL i cts) rv sb (type_memory_size u) mem)) /\
      abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
      ?u. evaluate_type E (EL i ts) = SOME u /\ mem_sz = type_memory_size u
Proof
  strip_tac >>
  qpat_x_assum `!t. MEM t ts ==> _` mp_tac >>
  simp[GSYM RIGHT_EXISTS_AND_THM] >>
  CONV_TAC (LAND_CONV (BINDER_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_IMP_THM)))) >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV SKOLEM_THM)) >>
  disch_then (qx_choose_then `f` assume_tac) >>
  qexists `MAP f ts` >> simp[] >> rpt strip_tac >>
  gvs[EL_MAP] >>
  qpat_x_assum `!t. _` (qspec_then `EL i ts` mp_tac) >>
  impl_tac >- (simp[MEM_EL] >> qexists `i` >> simp[]) >> strip_tac >>
  `?u. evaluate_type E (EL i ts) = SOME u` by metis_tac[IS_SOME_EXISTS] >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  simp[abi_member_head_size_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> qexists `mem0` >> simp[]
QED

Theorem abi_encode_translated_uniform_source_upto:
  !tv E ty sf ce E0.
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  abi_sfields_consistent_upto (type_value_size tv) sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) ==>
  ?ct.
    (!u. evaluate_type E ty = SOME u ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E ty)) /\
    (!u v av sb mem0.
      evaluate_type E ty = SOME u /\ value_has_type u v /\
      vyper_to_abi E ty v = SOME av /\ val_in_memory u v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
        !mem. val_in_memory u v sb mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv sb (type_memory_size u) mem)
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  Cases_on `ty`
  >~ [`BaseT b`] >- suspend "base"
  >~ [`ArrayT elem bd`] >- suspend "array"
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`StructT k`] >- suspend "struct"
  >~ [`FlagT k`] >- suspend "flag"
  >~ [`NoneT`] >- (qexists `Tuple []` >> simp[vyper_to_abi_type_def] >>
    rpt strip_tac >> gvs[vyper_to_abi_def, AllCaseEqs()] >>
    qexists `ListV []` >> simp[abi_encode_none_open_input])
  >> gvs[Once evaluate_type_def]
QED

Resume abi_encode_translated_uniform_source_upto[base]:
  `abi_enc_plan E (BaseT b) (type_to_abi_enc_info sf ce (BaseT b))` by
    (Cases_on `b` >>
     simp[type_to_abi_enc_info_def, abi_enc_plan_bytes, abi_enc_plan_string]
     >~ [`BytesT bd`] >- (Cases_on `bd` >>
       simp[type_to_abi_enc_info_def, abi_enc_plan_bytes] >>
       irule abi_encode_plan_static_copy >> simp[is_abi_dynamic_def] >>
       first_assum (irule_at Any) >> simp[]) >>
     irule abi_encode_plan_static_copy >> simp[is_abi_dynamic_def] >>
     first_assum (irule_at Any) >> simp[]) >>
  drule (cj 1 abi_encoder_uniform_value_source) >> simp[]
QED
Resume abi_encode_translated_uniform_source_upto[flag]:
  pure_rewrite_tac[type_to_abi_enc_info_def] >>
  irule abi_encode_translated_uniform_static >> simp[is_abi_dynamic_def] >>
  first_assum (irule_at Any) >> simp[]
QED
Resume abi_encode_translated_uniform_source_upto[array]:
  drule evaluate_type_array_child_size >> strip_tac >>
  `abi_sfields_consistent_upto (type_value_size u) sf E` by
    (irule abi_sfields_consistent_upto_mono >>
     qexists `type_value_size tv` >> simp[]) >>
  `?ect.
    (!u. evaluate_type E elem = SOME u ==>
      is_dynamic ect = is_dynamic (vyper_to_abi_type E elem) /\
      abi_member_head_size ect = abi_member_head_size (vyper_to_abi_type E elem)) /\
    (!u v av sb mem0.
      evaluate_type E elem = SOME u /\ value_has_type u v /\
      vyper_to_abi E elem v = SOME av /\ val_in_memory u v sb mem0 ==>
      ?rv. enc ect rv = enc (vyper_to_abi_type E elem) av /\
        !mem. val_in_memory u v sb mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce elem) ect rv sb (type_memory_size u) mem)` by
    (first_x_assum drule >> disch_then irule >> simp[] >>
     qexists `E0` >> simp[]) >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  Cases_on `bd`
  >- (pure_once_rewrite_tac[type_to_abi_enc_info_def] >> IF_CASES_TAC
      >- (irule abi_encode_translated_uniform_static >> simp[is_abi_dynamic_def] >>
          first_assum (irule_at Any) >> simp[]) >>
      irule abi_encoder_uniform_sarray >>
      conj_tac >- gvs[is_abi_dynamic_def] >>
      conj_tac >- (qexists `REPLICATE n ect` >>
      gvs[GSYM REPLICATE_GENLIST, EL_REPLICATE, abi_member_head_size_def] >>
      rpt gen_tac >> strip_tac >> gvs[EL_REPLICATE] >>
      first_assum MATCH_ACCEPT_TAC) >>
      simp[GSYM REPLICATE_GENLIST] >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      simp[abi_member_head_size_def]) >>
  pure_once_rewrite_tac[type_to_abi_enc_info_def] >>
  qexists `Array NONE ect` >>
  drule_all abi_encoder_uniform_dynarray >>
  simp[abi_member_head_size_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
  metis_tac[]
QED
Resume abi_encode_translated_uniform_source_upto[tuple]:
  pure_once_rewrite_tac[type_to_abi_enc_info_def] >>
  IF_CASES_TAC
  >- (irule abi_encode_translated_uniform_static >> simp[] >>
      first_assum (irule_at Any) >> simp[]) >>
  `!t. MEM t ts ==> IS_SOME (evaluate_type E t) /\ ?ct.
    (!u. evaluate_type E t = SOME u ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E t) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E t)) /\
    (!u v av sb mem0.
      evaluate_type E t = SOME u /\ value_has_type u v /\
      vyper_to_abi E t v = SOME av /\ val_in_memory u v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E t) av /\
        !mem. val_in_memory u v sb mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce t) ct rv sb (type_memory_size u) mem)` by
    (gen_tac >> strip_tac >>
     `?u. evaluate_type E t = SOME u /\ type_value_size u < type_value_size tv` by
       metis_tac[evaluate_type_tuple_child_size] >>
     `abi_sfields_consistent_upto (type_value_size u) sf E` by
       (irule abi_sfields_consistent_upto_mono >>
        qexists `type_value_size tv` >> simp[]) >>
     conj_tac >- simp[] >>
     first_x_assum drule >> disch_then irule >> simp[] >>
     qexists `E0` >> simp[]) >>
  drule_all abi_encode_translated_uniform_members >> strip_tac >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  qexists `Tuple cts` >> irule abi_encoder_uniform_tuple >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _` drule >> simp[] >>
  strip_tac >> first_assum (irule o cj 2 o cj 1)
QED
Resume abi_encode_translated_uniform_source_upto[struct]:
  `?args. FLOOKUP E k = SOME (StructArgs args)` by
    (qpat_x_assum `evaluate_type E (StructT k) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  `?fields. FLOOKUP sf (nsid_to_string k) = SOME fields /\
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (irule abi_sfields_consistent_upto_lookup >>
     qexistsl [`E`, `type_value_size tv`, `tv`] >> simp[]) >>
  pure_once_rewrite_tac[type_to_abi_enc_info_def] >>
  IF_CASES_TAC
  >- (irule abi_encode_translated_uniform_static >> simp[] >>
      first_assum (irule_at Any) >> simp[]) >>
  `!t. MEM t (MAP SND args) ==> IS_SOME (evaluate_type (E \\ k) t) /\ ?ct.
    (!u. evaluate_type (E \\ k) t = SOME u ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type (E \\ k) t) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type (E \\ k) t)) /\
    (!u v av sb mem0.
      evaluate_type (E \\ k) t = SOME u /\ value_has_type u v /\
      vyper_to_abi (E \\ k) t v = SOME av /\ val_in_memory u v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type (E \\ k) t) av /\
        !mem. val_in_memory u v sb mem ==>
          abi_encoder_open_input (type_to_abi_enc_info (sf \\ nsid_to_string k) ce t) ct rv sb (type_memory_size u) mem)` by
    (gen_tac >> strip_tac >>
     `?u. evaluate_type (E \\ k) t = SOME u /\ type_value_size u < type_value_size tv` by
       metis_tac[evaluate_type_struct_child_size] >>
     `abi_sfields_consistent_upto (type_value_size u) (sf \\ nsid_to_string k) (E \\ k)` by
       (irule abi_sfields_consistent_upto_domsub >> simp[] >>
        qexists `type_value_size tv` >> simp[]) >>
     conj_tac >- simp[] >>
     first_x_assum drule >> disch_then irule >> simp[] >>
     qexists `E0` >> simp[] >> irule SUBMAP_TRANS >> qexists `E` >> simp[]) >>
  `E \\ k SUBMAP E0` by (irule SUBMAP_TRANS >> qexists `E` >> simp[]) >>
  drule_all abi_encode_translated_uniform_members >> strip_tac >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  pure_rewrite_tac[LET_DEF] >> BETA_TAC >>
  qpat_assum `FLOOKUP sf _ = SOME fields` (rewrite_tac o single) >>
  rewrite_tac[option_case_def] >> BETA_TAC >>
  `MAP (\(fn,fty,sz).
      (type_to_abi_enc_info (sf \\ nsid_to_string k) ce fty,
       abi_embedded_static_size ce.ce_struct_fields fty, type_memory_bytes ce fty,
       is_abi_dynamic ce.ce_struct_fields fty)) fields =
   MAP (\t. (type_to_abi_enc_info (sf \\ nsid_to_string k) ce t,
       abi_embedded_static_size ce.ce_struct_fields t, type_memory_bytes ce t,
       is_abi_dynamic ce.ce_struct_fields t)) (MAP SND args)` by
    (qpat_x_assum `MAP (FST o SND) fields = MAP SND args`
       (once_rewrite_tac o single o GSYM) >>
     simp[MAP_MAP_o, o_DEF, pairTheory.LAMBDA_PROD]) >>
  qexists `Tuple cts` >> irule abi_encoder_uniform_struct >> gvs[] >>
  reverse conj_tac
  >- metis_tac[LENGTH_MAP] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _` drule >>
  disch_then drule >> strip_tac >> first_assum irule
QED
Finalise abi_encode_translated_uniform_source_upto

Theorem abi_encode_translated_uniform_source:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) ==>
  ?ct.
    (!u. evaluate_type E ty = SOME u ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E ty)) /\
    (!u v av sb mem0.
      evaluate_type E ty = SOME u /\ value_has_type u v /\
      vyper_to_abi E ty v = SOME av /\ val_in_memory u v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
        !mem. val_in_memory u v sb mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv sb (type_memory_size u) mem)
Proof
  strip_tac >> irule abi_encode_translated_uniform_source_upto >> simp[] >>
  conj_tac >- (qexists `E0` >> simp[]) >>
  irule abi_sfields_consistent_upto_init >> simp[]
QED
