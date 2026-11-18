Theory bodyFullAbiEncodeUniformTranslation
Ancestors
  bodyFullAbiEncodeUniformPrimitive bodyFullAbiEncodeUniformMembers
  bodyFullAbiEncodeUniformArray bodyFullAbiEncodeUniformAggregate
  exprSimAbiEncodeSourceTranslation exprSimAbiEncodePlanDomain
  exprSimAbiEncodePlanTranslation exprSimAbiEncodePlanMetadata abiEmptyDispatch
  abiEncoderOpenInput abiEncoderInput exprLowering compileEnv abiTypeBoundProps
  abiDecodeRanges contractABI finite_map list rich_list option vyperTypeSystem vyperValue vyperABI pair combin

Theorem abi_encode_uniform_source_upto[local]:
  !tv E ty sf ce E0.
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  abi_sfields_consistent_upto (type_value_size tv) sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) ==>
  ?ct.
    (!tv. evaluate_type E ty = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E ty)) /\
    (!tv v av. evaluate_type E ty = SOME tv /\ value_has_type tv v /\
      vyper_to_abi E ty v = SOME av ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
        !mem a. val_in_memory tv v a mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv a (type_memory_size tv) mem)
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  Cases_on `ty`
  >~ [`BaseT b`] >- (irule abi_encode_uniform_primitive >> simp[] >> qexists `E0` >> simp[])
  >~ [`ArrayT elem bd`] >- suspend "array"
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`StructT k`] >- suspend "struct"
  >~ [`FlagT k`] >- (irule abi_encode_uniform_primitive >> simp[] >> qexists `E0` >> simp[])
  >~ [`NoneT`] >- (irule abi_encode_uniform_primitive >> simp[] >> qexists `E0` >> simp[])
  >> gvs[Once evaluate_type_def]
QED

Resume abi_encode_uniform_source_upto[array]:
  drule evaluate_type_array_child_size >> strip_tac >>
  `abi_sfields_consistent_upto (type_value_size u) sf E` by
    (irule abi_sfields_consistent_upto_mono >> qexists `type_value_size tv` >> simp[]) >>
  `?ect.
    (!tv. evaluate_type E elem = SOME tv ==>
      is_dynamic ect = is_dynamic (vyper_to_abi_type E elem) /\
      abi_member_head_size ect = abi_member_head_size (vyper_to_abi_type E elem)) /\
    (!tv v av. evaluate_type E elem = SOME tv /\ value_has_type tv v /\
      vyper_to_abi E elem v = SOME av ==>
      ?rv. enc ect rv = enc (vyper_to_abi_type E elem) av /\
        !mem a. val_in_memory tv v a mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce elem) ect rv a (type_memory_size tv) mem)` by
    (first_x_assum drule >> disch_then irule >> simp[] >> qexists `E0` >> simp[]) >>
  Cases_on `bd` >> simp_tac pure_ss [Once type_to_abi_enc_info_def]
  >- (IF_CASES_TAC >- (drule_all abi_encode_uniform_static_copy >> simp[]) >>
      pure_rewrite_tac[GSYM REPLICATE_GENLIST] >> suspend "fixed") >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  qexists `Array NONE ect` >>
  drule_all abi_encode_uniform_dynarray >>
  disch_then (qspec_then `n` mp_tac) >>
  gvs[abi_member_head_size_def]
QED

Resume abi_encode_uniform_source_upto[fixed]:
  `!t. MEM t (REPLICATE n elem) ==> IS_SOME (evaluate_type E t) /\
    ?ct.
      (!tv. evaluate_type E t = SOME tv ==>
        is_dynamic ct = is_dynamic (vyper_to_abi_type E t) /\
        abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E t)) /\
      (!tv v av. evaluate_type E t = SOME tv /\ value_has_type tv v /\
        vyper_to_abi E t v = SOME av ==>
        ?rv. enc ct rv = enc (vyper_to_abi_type E t) av /\
          !mem a. val_in_memory tv v a mem ==>
            abi_encoder_open_input (type_to_abi_enc_info sf ce t) ct rv a (type_memory_size tv) mem)` by
    (simp[MEM_REPLICATE] >> rpt strip_tac >> qexists `ect` >> simp[]) >>
  drule_all abi_encode_uniform_members_map >> strip_tac >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  irule abi_encode_uniform_sarray >>
  conj_tac >- gvs[is_abi_dynamic_def] >>
  reverse conj_tac >- gvs[] >>
  qexists `cts` >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH (REPLICATE n elem) ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[EL_REPLICATE]
QED
Resume abi_encode_uniform_source_upto[tuple]:
  pure_rewrite_tac[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC >- (drule_all abi_encode_uniform_static_copy >> simp[]) >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  `!t. MEM t ts ==> IS_SOME (evaluate_type E t) /\
    ?ct.
      (!tv. evaluate_type E t = SOME tv ==>
        is_dynamic ct = is_dynamic (vyper_to_abi_type E t) /\
        abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E t)) /\
      (!tv v av. evaluate_type E t = SOME tv /\ value_has_type tv v /\
        vyper_to_abi E t v = SOME av ==>
        ?rv. enc ct rv = enc (vyper_to_abi_type E t) av /\
          !mem a. val_in_memory tv v a mem ==>
            abi_encoder_open_input (type_to_abi_enc_info sf ce t) ct rv a (type_memory_size tv) mem)` by
    (gen_tac >> strip_tac >>
     `?u. evaluate_type E t = SOME u /\ type_value_size u < type_value_size tv` by
       metis_tac[evaluate_type_tuple_child_size] >>
     `abi_sfields_consistent_upto (type_value_size u) sf E` by
       (irule abi_sfields_consistent_upto_mono >> qexists `type_value_size tv` >> simp[]) >>
     conj_tac >- simp[] >>
     first_x_assum drule >> disch_then irule >> simp[] >> qexists `E0` >> simp[]) >>
  drule_all abi_encode_uniform_members_map >> strip_tac >>
  qexists `Tuple cts` >> irule abi_encode_uniform_tuple >>
  simp[EL_MAP] >> reverse conj_tac >- gvs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH ts ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[EL_MAP]
QED
Resume abi_encode_uniform_source_upto[struct]:
  `?args. FLOOKUP E k = SOME (StructArgs args)` by
    (qpat_x_assum `evaluate_type E (StructT k) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  drule abi_sfields_consistent_upto_lookup >>
  disch_then drule >> disch_then drule >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields (StructT k)`
  >- suspend "dynamic_struct" >>
  simp[Once type_to_abi_enc_info_def] >>
  drule_all abi_encode_uniform_static_copy >> simp[]
QED
Resume abi_encode_uniform_source_upto[dynamic_struct]:
  `LENGTH fields = LENGTH args` by
    (qpat_x_assum `MAP FST fields = MAP FST args` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[LENGTH_MAP]) >>
  drule_all abi_empty_struct_descriptor >> disch_then SUBST1_TAC >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  `!t. MEM t (MAP SND args) ==> IS_SOME (evaluate_type (E \\ k) t) /\
    ?ct.
      (!tv. evaluate_type (E \\ k) t = SOME tv ==>
        is_dynamic ct = is_dynamic (vyper_to_abi_type (E \\ k) t) /\
        abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type (E \\ k) t)) /\
      (!tv v av. evaluate_type (E \\ k) t = SOME tv /\ value_has_type tv v /\
        vyper_to_abi (E \\ k) t v = SOME av ==>
        ?rv. enc ct rv = enc (vyper_to_abi_type (E \\ k) t) av /\
          !mem a. val_in_memory tv v a mem ==>
            abi_encoder_open_input (type_to_abi_enc_info (sf \\ nsid_to_string k) ce t) ct rv a
              (type_memory_size tv) mem)` by
    (gen_tac >> strip_tac >>
     `?u. evaluate_type (E \\ k) t = SOME u /\ type_value_size u < type_value_size tv` by
       metis_tac[evaluate_type_struct_child_size] >>
     `abi_sfields_consistent_upto (type_value_size u) (sf \\ nsid_to_string k) (E \\ k)` by
       (irule abi_sfields_consistent_upto_domsub >>
        simp[] >> qexists `type_value_size tv` >> simp[]) >>
     conj_tac >- simp[] >>
     first_x_assum drule >> disch_then irule >> simp[] >>
     qexists `E0` >> simp[] >> irule SUBMAP_TRANS >> qexists `E` >> simp[]) >>
  `E \\ k SUBMAP E0` by (irule SUBMAP_TRANS >> qexists `E` >> simp[]) >>
  drule_all abi_encode_uniform_members_map >> strip_tac >>
  qexists `Tuple cts` >> irule abi_encode_uniform_struct >>
  gvs[EL_MAP] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH cts ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >> gvs[EL_MAP]
QED
Finalise abi_encode_uniform_source_upto

Theorem abi_encode_uniform_translated_source:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) ==>
  ?ct.
    (!tv. evaluate_type E ty = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E ty)) /\
    (!tv v av. evaluate_type E ty = SOME tv /\ value_has_type tv v /\
      vyper_to_abi E ty v = SOME av ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
        !mem a. val_in_memory tv v a mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv a (type_memory_size tv) mem)
Proof
  strip_tac >> irule abi_encode_uniform_source_upto >> simp[] >>
  conj_tac >- (qexists `E0` >> simp[]) >>
  irule abi_sfields_consistent_upto_init >> simp[]
QED
