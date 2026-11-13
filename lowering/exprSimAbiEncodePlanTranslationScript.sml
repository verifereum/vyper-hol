(* Namespace-free plan assembly uses fixed full-environment layout metadata. *)
Theory exprSimAbiEncodePlanTranslation
Ancestors
  exprSimAbiEncodePlanMetadata retAbiPlanProps abiTypeBoundProps
  compileEnv exprLowering abiEncoderProps finite_map list rich_list option
  vyperTypeSystem vyperValue vyperABI pair combin

Theorem abi_encode_map_field_types[local]:
  !fields. MAP (\(fn, fty, sz). g fty) fields = MAP g (MAP (FST o SND) fields)
Proof
  Induct >> simp[FORALL_PROD]
QED

Theorem abi_encode_plan_static_copy:
  E SUBMAP E0 /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v) /\
  evaluate_type E ty = SOME tv /\
  ~is_abi_dynamic ce.ce_struct_fields ty ==>
  abi_enc_plan E ty (AbiCopy (type_memory_bytes ce ty))
Proof
  strip_tac >> drule_all abi_encode_element_metadata >> strip_tac >> gvs[] >>
  irule abi_enc_plan_copy >> fs[]
QED

Theorem abi_encode_plans_map:
  !ts.
  E SUBMAP E0 /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v) /\
  (!t. MEM t ts ==> IS_SOME (evaluate_type E t) /\ abi_enc_plan E t (f t)) ==>
  abi_enc_plans E ts
    (MAP (\t. (f t, abi_embedded_static_size ce.ce_struct_fields t,
      type_memory_bytes ce t, is_abi_dynamic ce.ce_struct_fields t)) ts)
Proof
  Induct >> simp[abi_enc_plan_nil] >> rpt strip_tac >>
  `?tv. evaluate_type E h = SOME tv` by
    (first_x_assum (qspec_then `h` mp_tac) >> simp[IS_SOME_EXISTS]) >>
  drule_all abi_encode_element_metadata >> strip_tac >> simp[] >>
  irule abi_enc_plan_cons >> simp[]
QED

Theorem abi_encode_plan_array:
  evaluate_type E (ArrayT elem bd) = SOME tv /\
  evaluate_type E elem = SOME etv /\
  abi_enc_plan E elem (type_to_abi_enc_info sf ce elem) /\
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v) ==>
  abi_enc_plan E (ArrayT elem bd) (type_to_abi_enc_info sf ce (ArrayT elem bd))
Proof
  strip_tac >> Cases_on `bd` >> simp[Once type_to_abi_enc_info_def]
  >- (IF_CASES_TAC >- (drule_all abi_encode_plan_static_copy >> simp[]) >>
      simp[GSYM REPLICATE_GENLIST] >>
      qpat_x_assum `evaluate_type E elem = _` assume_tac >>
      drule_all abi_encode_element_metadata >> strip_tac >>
      irule abi_enc_plan_sarray >> gvs[is_abi_dynamic_def] >>
      drule_all abi_enc_plans_replicate >>
      disch_then (qspec_then `n` mp_tac) >> gvs[]) >>
  qpat_x_assum `evaluate_type E elem = _` assume_tac >>
  drule_all abi_encode_element_metadata >> strip_tac >> simp[] >>
  irule abi_enc_plan_dynarray >> simp[]
QED

Theorem abi_encode_plan_upto:
  !tv E ty sf ce E0.
  assignable_type E ty /\ evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  abi_sfields_consistent_upto (type_value_size tv) sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v) ==>
  abi_enc_plan E ty (type_to_abi_enc_info sf ce ty)
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  Cases_on `ty`
  >~ [`BaseT b`] >- suspend "base"
  >~ [`ArrayT elem bd`] >- suspend "array"
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`StructT k`] >- suspend "struct"
  >~ [`FlagT k`] >- suspend "flag"
  >> fs[assignable_type_def]
QED

Resume abi_encode_plan_upto[base]:
  Cases_on `b` >>
  simp[type_to_abi_enc_info_def, abi_enc_plan_bytes, abi_enc_plan_string]
  >~ [`BytesT bd`] >- (Cases_on `bd` >>
    simp[type_to_abi_enc_info_def, abi_enc_plan_bytes] >>
    irule abi_encode_plan_static_copy >> simp[is_abi_dynamic_def] >>
    first_assum (irule_at Any) >> simp[]) >>
  irule abi_encode_plan_static_copy >> simp[is_abi_dynamic_def] >>
  first_assum (irule_at Any) >> simp[]
QED
Resume abi_encode_plan_upto[array]:
  drule evaluate_type_array_child_size >> strip_tac >>
  `assignable_type E elem` by fs[assignable_type_def] >>
  `abi_sfields_consistent_upto (type_value_size u) sf E` by
    (irule abi_sfields_consistent_upto_mono >>
     qexists `type_value_size tv` >> simp[]) >>
  `abi_enc_plan E elem (type_to_abi_enc_info sf ce elem)` by
    (first_x_assum drule >> disch_then irule >> simp[] >>
     qexists `E0` >> simp[]) >>
  drule_all abi_encode_plan_array >> simp[]
QED
Resume abi_encode_plan_upto[tuple]:
  simp[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC >- (drule_all abi_encode_plan_static_copy >> simp[]) >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  irule abi_enc_plan_tuple >> gvs[] >>
  irule abi_encode_plans_map >> simp[] >>
  reverse conj_tac >- (qexists `E0` >> simp[]) >>
  gen_tac >> strip_tac >>
  `?u. evaluate_type E t = SOME u /\ type_value_size u < type_value_size tv` by
    metis_tac[evaluate_type_tuple_child_size] >>
  `assignable_type E t` by fs[assignable_type_def, EVERY_MEM] >>
  `abi_sfields_consistent_upto (type_value_size u) sf E` by
    (irule abi_sfields_consistent_upto_mono >>
     qexists `type_value_size tv` >> simp[]) >>
  conj_tac >- simp[] >>
  first_x_assum drule >> disch_then irule >> simp[] >>
  qexists `E0` >> simp[]
QED
Resume abi_encode_plan_upto[struct]:
  `?args. FLOOKUP E k = SOME (StructArgs args)` by
    (qpat_x_assum `assignable_type E (StructT k)` mp_tac >>
     Cases_on `FLOOKUP E k` >> simp[assignable_type_def] >>
     Cases_on `x` >> simp[]) >>
  drule abi_sfields_consistent_upto_lookup >>
  disch_then drule >> disch_then drule >> simp[] >> strip_tac >>
  simp[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC >- (drule_all abi_encode_plan_static_copy >> simp[]) >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  simp[abi_encode_map_field_types] >>
  irule abi_enc_plan_struct >> conj_tac >- gvs[] >>
  qexists `args` >> simp[] >>
  irule abi_encode_plans_map >> simp[] >>
  reverse conj_tac
  >- (qexists `E0` >> simp[] >> irule SUBMAP_TRANS >> qexists `E` >> simp[]) >>
  gen_tac >> strip_tac >>
  `?u. evaluate_type (E \\ k) t = SOME u /\ type_value_size u < type_value_size tv` by
    metis_tac[evaluate_type_struct_child_size] >>
  `assignable_type (E \\ k) t` by
    fs[assignable_type_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  `abi_sfields_consistent_upto (type_value_size u) (sf \\ nsid_to_string k) (E \\ k)` by
    (irule abi_sfields_consistent_upto_domsub >>
     simp[] >> qexists `type_value_size tv` >> simp[]) >>
  conj_tac >- simp[] >>
  first_x_assum drule >> disch_then irule >> simp[] >>
  qexists `E0` >> simp[] >> irule SUBMAP_TRANS >> qexists `E` >> simp[]
QED
Resume abi_encode_plan_upto[flag]:
  simp[type_to_abi_enc_info_def] >>
  irule abi_encode_plan_static_copy >> simp[is_abi_dynamic_def] >>
  first_assum (irule_at Any) >> simp[]
QED
Finalise abi_encode_plan_upto

Theorem abi_encode_translated_plan:
  assignable_type E ty /\ evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v) ==>
  abi_enc_plan E ty (type_to_abi_enc_info sf ce ty)
Proof
  strip_tac >> irule abi_encode_plan_upto >> simp[] >>
  conj_tac >- (qexists `E0` >> simp[]) >>
  irule abi_sfields_consistent_upto_init >> simp[]
QED
