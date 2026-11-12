(* Compiler-selected uniform source representations, including empty types. *)
Theory bodyAbiEncodePlan
Ancestors
  abiEncoderLiveSource abiEncoderSourceTransport vyperABIValid
  bodyAbiEncodeMetadata abiTypeBoundProps abiEncoderSourceConstructors abiEncoderSourceProducer
  abiEncoderWindow abiEncoderProps exprLowering vyperABI vyperTypeSystem
  abiEncoderSourceAggregate abiEncoderOpenInput abiEncoderInput abiDecodeRanges contractABI
  vyperValue valueEncoding list rich_list finite_map

Theorem abi_encode_none_source_rep[local]:
  !env sf ce.
    source_rep env NoneT (type_to_abi_enc_info sf ce NoneT) (Tuple [])
Proof
  simp[source_rep_def, type_to_abi_enc_info_def,
       vyperValueTheory.evaluate_type_def, vyper_to_abi_type_def] >>
  rpt strip_tac >>
  gvs[vyperTypingTheory.value_has_type_def, vyper_to_abi_def] >>
  qexists_tac `ListV []` >>
  simp[valueEncodingTheory.type_memory_size_def,
       abi_encoder_open_complex_iff,
       abiEncoderInputTheory.abi_encoder_member_span_def,
       abiEncoderInputTheory.abi_encoder_tuple_type_def,
       contractABITheory.enc_def]
QED

Theorem abi_source_reps_map[local]:
  !ts.
  (!t. MEM t ts ==> ?ct tv.
    source_rep env t (f t) ct /\ evaluate_type env t = SOME tv /\
    abi_embedded_static_size ce.ce_struct_fields t =
      (if is_dynamic (vyper_to_abi_type env t) then 32
       else static_length (vyper_to_abi_type env t)) /\
    type_memory_bytes ce t = type_memory_size tv /\
    is_abi_dynamic ce.ce_struct_fields t = is_dynamic (vyper_to_abi_type env t)) ==>
  ?cts. source_reps env ts
    (MAP (\t. (f t, abi_embedded_static_size ce.ce_struct_fields t,
      type_memory_bytes ce t, is_abi_dynamic ce.ce_struct_fields t)) ts) cts
Proof
  Induct >- (strip_tac >> qexists_tac `[]` >> simp[source_reps_nil]) >>
  gen_tac >> disch_tac >>
  `?ct tv. source_rep env h (f h) ct /\ evaluate_type env h = SOME tv /\
    abi_embedded_static_size ce.ce_struct_fields h =
      (if is_dynamic (vyper_to_abi_type env h) then 32
       else static_length (vyper_to_abi_type env h)) /\
    type_memory_bytes ce h = type_memory_size tv /\
    is_abi_dynamic ce.ce_struct_fields h = is_dynamic (vyper_to_abi_type env h)`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  `?cts. source_reps env ts
    (MAP (\t. (f t, abi_embedded_static_size ce.ce_struct_fields t,
      type_memory_bytes ce t, is_abi_dynamic ce.ce_struct_fields t)) ts) cts`
    by (first_x_assum irule >> rpt strip_tac >>
        qpat_x_assum `!t. MEM t (h::ts) ==> _` (qspec_then `t` mp_tac) >> simp[]) >>
  qexists_tac `ct::cts` >> rewrite_tac [MAP] >> BETA_TAC >> irule source_reps_cons >> simp[] >>
  drule_all source_rep_metadata >> simp[abi_member_head_size_def]
QED

Theorem type_to_abi_enc_info_source_rep:
  !tv env ty sf ce env0.
  evaluate_type env ty = SOME tv /\
  abi_sfields_consistent_upto (type_value_size tv) sf env /\
  env SUBMAP env0 /\ sfields_tenv_consistent ce.ce_struct_fields env0 /\
  (!t tv. evaluate_type env0 t = SOME tv ==>
    type_memory_bytes ce t = type_memory_size tv) ==>
  ?ct. source_rep env ty (type_to_abi_enc_info sf ce ty) ct
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  Cases_on `ty`
  >~ [`BaseT bt`] >- suspend "base"
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`ArrayT t bd`] >- suspend "array"
  >~ [`StructT nsid`] >- suspend "struct"
  >~ [`FlagT nsid`] >- suspend "flag"
  >> metis_tac[abi_encode_none_source_rep]
QED

Resume type_to_abi_enc_info_source_rep[flag]:
  drule_all abi_source_metadata_reference >> strip_tac >>
  simp[type_to_abi_enc_info_def] >> irule source_rep_static_copy >>
  simp[vyper_to_abi_type_def, contractABITheory.is_dynamic_def]
QED

Resume type_to_abi_enc_info_source_rep[base]:
  drule_all abi_source_metadata_reference >> strip_tac >>
  Cases_on `bt` >> simp[type_to_abi_enc_info_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> simp[type_to_abi_enc_info_def]
      >- (irule source_rep_static_copy >>
          simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def]) >>
      irule (cj 1 abi_encoder_uniform_source) >> simp[abi_enc_plan_bytes])
  >~ [`StringT n`] >- (irule (cj 1 abi_encoder_uniform_source) >> simp[abi_enc_plan_string])
  >> irule source_rep_static_copy >>
  gvs[vyper_to_abi_type_def, vyper_base_to_abi_type_def,
      contractABITheory.is_dynamic_def]
QED
Resume type_to_abi_enc_info_source_rep[tuple]:
  drule_all abi_source_metadata_reference >> strip_tac >>
  simp[Once type_to_abi_enc_info_def] >> IF_CASES_TAC
  >- (irule source_rep_static_copy >> simp[]) >>
  `?cts. source_reps env ts
    (MAP (\t. (type_to_abi_enc_info sf ce t,
      abi_embedded_static_size ce.ce_struct_fields t,
      type_memory_bytes ce t, is_abi_dynamic ce.ce_struct_fields t)) ts) cts` by
    (irule abi_source_reps_map >> rpt strip_tac >>
     drule_all evaluate_type_tuple_child_size >> strip_tac >>
     `abi_sfields_consistent_upto (type_value_size u) sf env` by
       (irule abi_sfields_consistent_upto_mono >>
        qexists_tac `type_value_size tv` >> simp[]) >>
     `?ct. source_rep env t (type_to_abi_enc_info sf ce t) ct` by
       (first_x_assum (drule_then irule) >> simp[] >>
        qexists_tac `env0` >> simp[]) >>
     drule_all abi_source_metadata_reference >> strip_tac >>
     qexistsl_tac [`ct`, `u`] >> simp[]) >>
  qexists_tac `Tuple cts` >> irule source_rep_tuple >> simp[]
QED
Resume type_to_abi_enc_info_source_rep[array]:
  drule_all abi_source_metadata_reference >> strip_tac >>
  drule evaluate_type_array_child_size >> strip_tac >>
  `abi_sfields_consistent_upto (type_value_size u) sf env` by
    (irule abi_sfields_consistent_upto_mono >>
     qexists_tac `type_value_size tv` >> simp[]) >>
  `?ct. source_rep env t (type_to_abi_enc_info sf ce t) ct` by
    (first_x_assum (drule_then irule) >> simp[] >>
     qexists_tac `env0` >> simp[]) >>
  drule_all abi_source_metadata_reference >> strip_tac >>
  Cases_on `bd` >> simp[Once type_to_abi_enc_info_def]
  >- (IF_CASES_TAC
      >- (simp[] >> irule source_rep_static_copy >>
          gvs[vyper_to_abi_type_def, is_dynamic_def]) >>
      `?cts. source_reps env (REPLICATE n t)
        (MAP (\t. (type_to_abi_enc_info sf ce t,
          abi_embedded_static_size ce.ce_struct_fields t,
          type_memory_bytes ce t, is_abi_dynamic ce.ce_struct_fields t))
          (REPLICATE n t)) cts` by
        (irule abi_source_reps_map >> simp[MEM_REPLICATE] >>
         rpt strip_tac >> qexists_tac `ct` >> simp[]) >>
      Cases_on `n = 0`
      >- (gvs[] >> qexists_tac `Array (SOME 0) (Bytes NONE)` >>
          simp[source_rep_fixed_array_zero]) >>
      qexists_tac `Tuple cts` >> irule source_rep_fixed_array >>
      gvs[GSYM REPLICATE_GENLIST]) >>
  qexists_tac `Array NONE ct` >>
  irule source_rep_dynamic_array >> simp[]
QED
Resume type_to_abi_enc_info_source_rep[struct]:
  drule_all abi_source_metadata_reference >> strip_tac >>
  simp[Once type_to_abi_enc_info_def] >> IF_CASES_TAC
  >- (irule source_rep_static_copy >> simp[]) >>
  `?args. FLOOKUP env nsid = SOME (StructArgs args)` by
    (qpat_x_assum `evaluate_type env (StructT nsid) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  `?fields. FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
     MAP FST fields = MAP FST args /\
     MAP (FST o SND) fields = MAP SND args` by
    (irule abi_sfields_consistent_upto_lookup >>
     qexistsl_tac [`env`, `type_value_size tv`, `tv`] >> simp[]) >>
  `env \\ nsid SUBMAP env0` by
    (irule SUBMAP_TRANS >> qexists_tac `env` >> simp[]) >>
  simp[retAbiPlanPropsTheory.map_struct_field_types] >>
  `?cts. source_reps (env \\ nsid) (MAP SND args)
    (MAP (\t. (type_to_abi_enc_info (sf \\ nsid_to_string nsid) ce t,
      abi_embedded_static_size ce.ce_struct_fields t,
      type_memory_bytes ce t, is_abi_dynamic ce.ce_struct_fields t))
      (MAP SND args)) cts` by
    (irule abi_source_reps_map >> rpt strip_tac >>
     drule_all evaluate_type_struct_child_size >> strip_tac >>
     `abi_sfields_consistent_upto (type_value_size u)
        (sf \\ nsid_to_string nsid) (env \\ nsid)` by
       (irule abi_sfields_consistent_upto_domsub >> simp[] >>
        qexists_tac `type_value_size tv` >> simp[]) >>
     `?ct. source_rep (env \\ nsid) t
        (type_to_abi_enc_info (sf \\ nsid_to_string nsid) ce t) ct` by
       (first_x_assum (drule_then irule) >> simp[] >>
        qexists_tac `env0` >> simp[]) >>
     drule_all abi_source_metadata_reference >> strip_tac >>
     qexistsl_tac [`ct`, `u`] >> simp[]) >>
  qexists_tac `Tuple cts` >> irule source_rep_struct >>
  qexists_tac `args` >> simp[]
QED
Finalise type_to_abi_enc_info_source_rep


Theorem abi_encode_compiler_source_window:
  evaluate_type env ty = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields env /\
  (!t tv. evaluate_type env t = SOME tv ==>
     type_memory_bytes ce t = type_memory_size tv) /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v p mem ==>
  ?at rv. abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce ty)
      at rv p (val_footprint tv v) mem /\
    enc at rv = enc (vyper_to_abi_type env ty) av /\
    LENGTH (enc at rv) <= vyper_abi_size_bound env ty
Proof
  strip_tac >> Cases_on `val_footprint tv v = type_memory_size tv`
  >- (`?ct. source_rep env ty
        (type_to_abi_enc_info ce.ce_struct_fields ce ty) ct` by
        (irule type_to_abi_enc_info_source_rep >> simp[] >>
         conj_tac
         >- (qexists_tac `env` >> simp[]) >>
         simp[abi_sfields_consistent_upto_init]) >>
      drule_all source_rep_transport >> strip_tac >>
      drule abi_encoder_open_input_window >> strip_tac >>
      drule_all (cj 1 vyper_to_abi_enc_le_size_bound) >>
      strip_tac >> qexistsl_tac [`ct`, `rv`] >> gvs[]) >>
  drule_all abi_source_non_nominal_forms >> strip_tac >>
  `abi_enc_plan env ty (type_to_abi_enc_info ce.ce_struct_fields ce ty)` by
    (gvs[] >> simp[type_to_abi_enc_info_def, abi_enc_plan_bytes,
                  abi_enc_plan_string]) >>
  drule_all abi_encoder_live_source_window >> simp[]
QED
