(* Uniform aggregate constructors, independent of encoder plans. *)
Theory abiEncoderUniformAggregateConstructors
Ancestors
  abiEncoderUniformStaticSource abiEncoderUniformSourceMembers
  abiEncoderUniformSourceEncoding
  abiEncoderSourceProducer abiEncoderSourcePrimitive abiEncoderSourceTransport
  abiEncoderSourceAggregate abiEncoderSourceWindow abiEncoderProps abiCallerTupleLayout
  vyperABI contractABI abiDecodeRanges abiEncoderInput list rich_list
  valueEncodingProofs vyperValueOperation abiEncoderOpenInput vyperValue
  valueEncoding vyperTyping

Theorem uniform_list_ih_members[local]:
  LENGTH ts = LENGTH infos /\ LENGTH ts = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn.
    i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type env (EL i ts) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type env (EL i ts)) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type env (EL i ts))) /\
     (!tv v av sb mem0.
      evaluate_type env (EL i ts) = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env (EL i ts) v = SOME av /\ val_in_memory tv v sb mem0 ==>
      ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type env (EL i ts)) av /\
        !mem. val_in_memory tv v sb mem ==>
          abi_encoder_open_input ei (EL i cts) rv sb (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    ?tv. evaluate_type env (EL i ts) = SOME tv /\ mem_sz = type_memory_size tv) ==>
  source_reps env ts infos cts /\
  !tvs vs avs sb mem0.
    (!i. i < LENGTH ts ==>
      evaluate_type env (EL i ts) = SOME (EL i tvs) /\
      value_has_type (EL i tvs) (EL i vs) /\
      val_in_memory (EL i tvs) (EL i vs)
        (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem0 /\
      vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs)) ==>
    LENGTH tvs = LENGTH ts /\ LENGTH vs = LENGTH ts /\ LENGTH avs = LENGTH ts ==>
    ?rvs. LENGTH rvs = LENGTH ts /\
      (!i. i < LENGTH ts ==>
        enc (EL i cts) (EL i rvs) = enc (vyper_to_abi_type env (EL i ts)) (EL i avs)) /\
      !mem. (!i. i < LENGTH ts ==>
        val_in_memory (EL i tvs) (EL i vs)
          (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
      !i ei abi_sz mem_sz dyn.
        i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
        abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
        abi_encoder_open_input ei (EL i cts) (EL i rvs)
          (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem
Proof
  strip_tac >>
  `source_reps env ts infos cts` by
    (simp[source_reps_def] >> rpt strip_tac >>
     qpat_x_assum `!i ei abi_sz mem_sz dyn. _` (qspec_then `i` mp_tac) >>
     simp[source_rep_def] >> metis_tac[]) >>
  conj_tac >- simp[] >> rpt gen_tac >> ntac 2 strip_tac >>
  irule abi_encoder_uniform_source_members >> simp[] >>
  rpt strip_tac >>
  Cases_on `EL i infos` >> PairCases_on `r` >>
  qpat_assum `!i ei abi_sz mem_sz dyn. _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >> metis_tac[]
QED

Theorem abi_encoder_uniform_tuple:
  is_dynamic (vyper_to_abi_type env (TupleT ts)) /\
  LENGTH ts = LENGTH infos /\ LENGTH ts = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn.
    i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type env (EL i ts) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type env (EL i ts)) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type env (EL i ts))) /\
     (!tv v av sb mem0.
      evaluate_type env (EL i ts) = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env (EL i ts) v = SOME av /\ val_in_memory tv v sb mem0 ==>
      ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type env (EL i ts)) av /\
        !mem. val_in_memory tv v sb mem ==>
          abi_encoder_open_input ei (EL i cts) rv sb (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    ?tv. evaluate_type env (EL i ts) = SOME tv /\ mem_sz = type_memory_size tv) ==>
  (!tv. evaluate_type env (TupleT ts) = SOME tv ==>
    is_dynamic (Tuple cts) = is_dynamic (vyper_to_abi_type env (TupleT ts)) /\
    abi_member_head_size (Tuple cts) = abi_member_head_size (vyper_to_abi_type env (TupleT ts))) /\
  (!tv v av sb mem0.
    evaluate_type env (TupleT ts) = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env (TupleT ts) v = SOME av /\ val_in_memory tv v sb mem0 ==>
    ?rv. enc (Tuple cts) rv = enc (vyper_to_abi_type env (TupleT ts)) av /\
      !mem. val_in_memory tv v sb mem ==>
        abi_encoder_open_input (AbiComplex infos) (Tuple cts) rv sb (type_memory_size tv) mem)
Proof
  strip_tac >>
  drule_all uniform_list_ih_members >> strip_tac >>
  pop_assum (mk_asm "members") >>
  drule source_reps_any_dynamic >> strip_tac >>
  drule source_reps_tuple_head >> strip_tac >>
  simp[vyper_to_abi_type_def] >> rpt strip_tac >>
  `?tvs. tv = TupleTV tvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (ArrayV (TupleV vs)) _ _` >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_tuple_parent >>
  simp[value_has_type_def] >>
  disch_then (qspecl_then [`ts`, `env`, `av`] mp_tac) >>
  simp[] >> strip_tac >> pop_assum (mk_asm "typed") >> gvs[] >>
  asm_x "members" mp_tac >> simp[] >> disch_tac >>
  asm "typed" assume_tac >>
  qpat_x_assum `!tvs vs avs sb mem0. _` drule >>
  simp[] >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _` kall_tac >>
  qexists_tac `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
       enc (Tuple (vyper_to_abi_types env ts)) (ListV avs)` by
        (irule abi_encoder_source_reps_encoding_cong >>
         simp[abi_encoder_tuple_type_def] >> metis_tac[LENGTH_MAP]) >>
      gvs[Once enc_def]) >>
  rpt strip_tac >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_tuple_parent >>
  simp[value_has_type_def] >>
  disch_then (qspecl_then [`ts`, `env`, `ListV avs`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  irule abi_encoder_source_complex_input >> conj_tac
  >- (`!i. i < LENGTH ts ==>
         evaluate_type env (EL i ts) = SOME (EL i tvs)` by simp[] >>
      `LENGTH tvs = LENGTH ts` by simp[] >>
      drule_all source_reps_full_span >>
      simp[type_memory_size_def, type_memory_size_list_sum]) >>
  qexists_tac `cts` >>
  drule source_reps_lengths >> simp[abi_encoder_tuple_type_def] >>
  metis_tac[source_reps_index]
QED

Theorem abi_encoder_uniform_sarray:
  is_dynamic (vyper_to_abi_type env t) /\
  LENGTH (REPLICATE n t) = LENGTH infos /\ LENGTH (REPLICATE n t) = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn.
    i < LENGTH (REPLICATE n t) /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type env (EL i (REPLICATE n t)) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type env (EL i (REPLICATE n t))) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type env (EL i (REPLICATE n t)))) /\
     (!tv v av sb mem0.
      evaluate_type env (EL i (REPLICATE n t)) = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env (EL i (REPLICATE n t)) v = SOME av /\ val_in_memory tv v sb mem0 ==>
      ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type env (EL i (REPLICATE n t))) av /\
        !mem. val_in_memory tv v sb mem ==>
          abi_encoder_open_input ei (EL i cts) rv sb (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    ?tv. evaluate_type env (EL i (REPLICATE n t)) = SOME tv /\ mem_sz = type_memory_size tv) ==>
  ?ct.
    (!tv. evaluate_type env (ArrayT t (Fixed n)) = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type env (ArrayT t (Fixed n))) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type env (ArrayT t (Fixed n)))) /\
    (!tv v av sb mem0.
      evaluate_type env (ArrayT t (Fixed n)) = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env (ArrayT t (Fixed n)) v = SOME av /\ val_in_memory tv v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type env (ArrayT t (Fixed n))) av /\
        !mem. val_in_memory tv v sb mem ==>
          abi_encoder_open_input (AbiComplex infos) ct rv sb (type_memory_size tv) mem)
Proof
  strip_tac >> drule_all uniform_list_ih_members >> strip_tac >>
  pop_assum (mk_asm "members") >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. i < _ /\ _ ==> _` kall_tac >>
  Cases_on `n = 0`
  >- (gvs[] >> drule source_reps_lengths >> strip_tac >> gvs[] >>
      qexists_tac `Array (SOME 0) (Bytes NONE)` >>
      simp[vyper_to_abi_type_def, is_dynamic_def, abi_member_head_size_def] >>
      rpt strip_tac >>
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
  simp[vyper_to_abi_type_def, abi_member_head_size_def, is_dynamic_def] >>
  rpt strip_tac >>
  `?tv0. tv = ArrayTV tv0 (Fixed n)` by
    (qpat_x_assum `evaluate_type env (ArrayT t (Fixed n)) = SOME tv` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `tv = ArrayTV _ _` SUBST_ALL_TAC >>
  qpat_x_assum `value_has_type _ v` mp_tac >>
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> simp[value_has_type_def] >> strip_tac >>
  rename1 `val_in_memory _ (ArrayV (SArrayV kvs)) _ _` >>
  qpat_x_assum `vyper_to_abi env _ _ = SOME av` mp_tac >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `evaluate_type env (ArrayT t (Fixed n)) = _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `tv = tv0` SUBST_ALL_TAC >>
  qpat_x_assum `ListV avs = av` (SUBST_ALL_TAC o SYM) >>
  `value_has_type (ArrayTV tv0 (Fixed n)) (ArrayV (SArrayV kvs))` by
    simp[value_has_type_def] >>
  drule_all abi_encoder_sparse_source >> strip_tac >>
  qabbrev_tac `vs = array_elements (ArrayTV tv0 (Fixed n)) (SArrayV kvs)` >>
  `LENGTH vs = n` by
    simp[Abbr `vs`, array_elements_def] >>
  `!i. i < LENGTH (REPLICATE n t) ==>
    evaluate_type env (EL i (REPLICATE n t)) = SOME (EL i (REPLICATE n tv0)) /\
    value_has_type (EL i (REPLICATE n tv0)) (EL i vs) /\
    val_in_memory (EL i (REPLICATE n tv0)) (EL i vs)
      (sb + SUM (MAP type_memory_size (TAKE i (REPLICATE n tv0)))) mem0 /\
    vyper_to_abi env (EL i (REPLICATE n t)) (EL i vs) = SOME (EL i avs)` by
    (asm_x "members" kall_tac >>
     qpat_x_assum `LENGTH vs = n` kall_tac >>
     qpat_x_assum `LENGTH avs = n` kall_tac >>
     qpat_x_assum `LENGTH (REPLICATE n t) = LENGTH infos` kall_tac >>
     qpat_x_assum `LENGTH (REPLICATE n t) = LENGTH cts` kall_tac >>
     simp[EL_REPLICATE] >> rpt strip_tac >>
     simp[REPLICATE_GENLIST, TAKE_GENLIST] >>
     simp[GSYM REPLICATE_GENLIST, arithmeticTheory.MIN_DEF,
          arithmeticTheory.MULT_COMM]) >>
  `LENGTH (REPLICATE n tv0) = LENGTH (REPLICATE n t) /\
   LENGTH vs = LENGTH (REPLICATE n t) /\ LENGTH avs = LENGTH (REPLICATE n t)` by
    (simp[NoAsms, LENGTH_REPLICATE] >> metis_tac[]) >>
  asm_x "members" drule >> disch_then drule_all >> strip_tac >>
  qpat_x_assum `LENGTH (REPLICATE n t) = LENGTH infos` kall_tac >>
  qpat_x_assum `LENGTH (REPLICATE n t) = LENGTH cts` kall_tac >>
  qpat_x_assum `LENGTH vs = n` kall_tac >>
  qpat_x_assum `LENGTH avs = n` kall_tac >>
  qexists_tac `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
       enc (Tuple (vyper_to_abi_types env (REPLICATE n t))) (ListV avs)` by
        (irule abi_encoder_source_reps_encoding_cong >>
         qexistsl_tac [`cts`, `env`, `infos`, `REPLICATE n t`] >>
         simp[abi_encoder_tuple_type_def]) >>
      gvs[Once enc_def, source_translation_list]) >>
  rpt strip_tac >>
  drule_all abi_encoder_sparse_source >> strip_tac >>
  `!i. i < LENGTH (REPLICATE n t) ==>
    val_in_memory (EL i (REPLICATE n tv0)) (EL i vs)
      (sb + SUM (MAP type_memory_size (TAKE i (REPLICATE n tv0)))) mem` by
    (qpat_x_assum `!mem. (!i. _) ==> _` kall_tac >>
     simp[EL_REPLICATE, Abbr `vs`] >> rpt strip_tac >>
     simp[REPLICATE_GENLIST, TAKE_GENLIST] >>
     simp[GSYM REPLICATE_GENLIST, arithmeticTheory.MIN_DEF,
          arithmeticTheory.MULT_COMM]) >>
  qpat_x_assum `!mem. (!i. _) ==> _` drule >> strip_tac >>
  irule abi_encoder_source_complex_input >> conj_tac
  >- (`!i. i < LENGTH (REPLICATE n t) ==>
         evaluate_type env (EL i (REPLICATE n t)) = SOME (EL i (REPLICATE n tv0))` by
        simp[EL_REPLICATE] >>
      drule_all source_reps_full_span >> simp[type_memory_size_def]) >>
  qexists_tac `cts` >> simp[abi_encoder_tuple_type_def]
QED

Theorem abi_encoder_uniform_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  is_dynamic (vyper_to_abi_type env (StructT nsid)) /\
  LENGTH (MAP SND args) = LENGTH infos /\ LENGTH (MAP SND args) = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn.
    i < LENGTH (MAP SND args) /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type (env \\ nsid) (EL i (MAP SND args)) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type (env \\ nsid) (EL i (MAP SND args))) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type (env \\ nsid) (EL i (MAP SND args)))) /\
     (!tv v av sb mem0.
      evaluate_type (env \\ nsid) (EL i (MAP SND args)) = SOME tv /\ value_has_type tv v /\
      vyper_to_abi (env \\ nsid) (EL i (MAP SND args)) v = SOME av /\ val_in_memory tv v sb mem0 ==>
      ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type (env \\ nsid) (EL i (MAP SND args))) av /\
        !mem. val_in_memory tv v sb mem ==>
          abi_encoder_open_input ei (EL i cts) rv sb (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    ?tv. evaluate_type (env \\ nsid) (EL i (MAP SND args)) = SOME tv /\ mem_sz = type_memory_size tv) ==>
  (!tv. evaluate_type env (StructT nsid) = SOME tv ==>
    is_dynamic (Tuple cts) = is_dynamic (vyper_to_abi_type env (StructT nsid)) /\
    abi_member_head_size (Tuple cts) = abi_member_head_size (vyper_to_abi_type env (StructT nsid))) /\
  (!tv v av sb mem0.
    evaluate_type env (StructT nsid) = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env (StructT nsid) v = SOME av /\ val_in_memory tv v sb mem0 ==>
    ?rv. enc (Tuple cts) rv = enc (vyper_to_abi_type env (StructT nsid)) av /\
      !mem. val_in_memory tv v sb mem ==>
        abi_encoder_open_input (AbiComplex infos) (Tuple cts) rv sb (type_memory_size tv) mem)
Proof
  strip_tac >> drule_all uniform_list_ih_members >> strip_tac >>
  pop_assum (mk_asm "members") >>
  drule source_reps_any_dynamic >> strip_tac >>
  drule source_reps_tuple_head >> strip_tac >>
  simp[vyper_to_abi_type_def] >> rpt strip_tac >>
  `?ftvs. tv = StructTV ftvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (StructV fields) _ _` >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_struct_parent >>
  simp[value_has_type_def] >>
  disch_then (qspecl_then [`nsid`, `env`, `av`] mp_tac) >>
  simp[] >> strip_tac >> pop_assum (mk_asm "typed") >> gvs[] >>
  asm_x "members" mp_tac >> simp[] >> disch_tac >>
  asm "typed" assume_tac >>
  qpat_x_assum `!tvs vs avs sb mem0. _` drule >>
  simp[] >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _` kall_tac >>
  qexists_tac `ListV rvs` >> conj_tac
  >- (`enc (Tuple cts) (ListV rvs) =
       enc (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args))) (ListV avs)` by
        (irule abi_encoder_source_reps_encoding_cong >>
         simp[abi_encoder_tuple_type_def] >> metis_tac[LENGTH_MAP]) >>
      gvs[Once enc_def]) >>
  rpt strip_tac >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_struct_parent >>
  simp[value_has_type_def] >>
  disch_then (qspecl_then [`nsid`, `env`, `ListV avs`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `tvs = tvs'` by metis_tac[MAP_ZIP, LENGTH_MAP] >> gvs[] >>
  irule abi_encoder_source_complex_input >> conj_tac
  >- (`!i. i < LENGTH (MAP SND args) ==>
         evaluate_type (env \\ nsid) (EL i (MAP SND args)) = SOME (EL i tvs)` by simp[] >>
      `LENGTH tvs = LENGTH (MAP SND args)` by simp[] >>
      drule_all source_reps_full_span >>
      simp[type_memory_size_def, type_memory_size_fields_sum, GSYM MAP_MAP_o, MAP_ZIP]) >>
  qexists_tac `cts` >>
  drule source_reps_lengths >> simp[abi_encoder_tuple_type_def] >>
  rpt strip_tac >>
  `i < LENGTH (MAP SND args)` by simp[] >>
  drule_all source_reps_index >> simp[]
QED
