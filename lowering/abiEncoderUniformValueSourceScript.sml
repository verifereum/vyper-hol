(* Uniform source values: select witnesses before varying memory. *)
Theory abiEncoderUniformValueSource
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

Theorem abi_encoder_uniform_value_source:
  (!env ty ei. abi_enc_plan env ty ei ==> ?ct.
    (!tv. evaluate_type env ty = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type env ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type env ty)) /\
    (!tv v av sb mem0.
      evaluate_type env ty = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env ty v = SOME av /\ val_in_memory tv v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
        !mem. val_in_memory tv v sb mem ==>
          abi_encoder_open_input ei ct rv sb (type_memory_size tv) mem)) /\
  (!env ts infos. abi_enc_plans env ts infos ==> ?cts.
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
      abi_sz = abi_member_head_size (EL i cts) /\
      dyn = is_dynamic (EL i cts) /\
      ?tv. evaluate_type env (EL i ts) = SOME tv /\ mem_sz = type_memory_size tv))
Proof
  ho_match_mp_tac abi_enc_plan_ind >> rpt conj_tac
  >- suspend "prim"
  >- suspend "bytes"
  >- suspend "string"
  >- suspend "static"
  >- suspend "dynarray"
  >- suspend "tuple"
  >- suspend "sarray"
  >- suspend "struct"
  >- (rpt strip_tac >> qexists_tac `[]` >> simp[])
  >> suspend "cons"
QED

Resume abi_encoder_uniform_value_source[bytes]:
  gen_tac >> gen_tac >> qexists_tac `Bytes NONE` >>
  simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
  rpt strip_tac >> qexists_tac `av` >> simp[] >> rpt strip_tac >>
  irule abi_encoder_open_bytes_source >> simp[] >>
  qexistsl_tac [`env`, `v`] >> simp[]
QED

Resume abi_encoder_uniform_value_source[string]:
  gen_tac >> gen_tac >> qexists_tac `String` >>
  simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
  rpt strip_tac >> qexists_tac `av` >> simp[] >> rpt strip_tac >>
  irule abi_encoder_open_string_source >> simp[] >>
  qexistsl_tac [`env`, `v`] >> simp[]
QED

Resume abi_encoder_uniform_value_source[static]:
  rpt strip_tac >> drule_all abi_encoder_uniform_static_value_source >>
  disch_then (qx_choose_then `ct` strip_assume_tac) >>
  drule_all abi_caller_static_memory >> strip_tac >>
  qexists_tac `ct` >> simp[abi_member_head_size_def] >> metis_tac[]
QED

Resume abi_encoder_uniform_value_source[prim]:
  rpt strip_tac >> Cases_on `?tv. evaluate_type env ty = SOME tv`
  >- (pop_assum (qx_choose_then `tv` assume_tac) >>
      drule_all abi_encoder_word_source_shape >> strip_tac >>
      drule_all abi_encoder_uniform_static_value_source >>
      disch_then (qx_choose_then `ct` strip_assume_tac) >>
      drule_all abi_caller_static_memory >> strip_tac >>
      qexists_tac `ct` >> simp[abi_member_head_size_def] >>
      metis_tac[abi_encoder_copy32_word]) >>
  qexists_tac `vyper_to_abi_type env ty` >> simp[] >> metis_tac[]
QED

Resume abi_encoder_uniform_value_source[cons]:
  rpt strip_tac >> qexists_tac `ct::cts` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `i`
  >- (gvs[] >> conj_tac
      >- (rpt strip_tac >> first_assum irule >> simp[] >>
          qexists_tac `mem0` >> simp[]) >>
      simp[abi_member_head_size_def]) >>
  gvs[] >> qpat_x_assum `!i ei abi_sz mem_sz dyn. _`
    (qspec_then `n` mp_tac) >> simp[] >>
  metis_tac[]
QED

Resume abi_encoder_uniform_value_source[dynarray]:
  rpt strip_tac >>
  `source_rep env ty ei ct` by (simp[source_rep_def] >> metis_tac[]) >>
  drule_all source_rep_metadata >> strip_tac >>
  qexists_tac `Array NONE ct` >>
  simp[vyper_to_abi_type_def, is_dynamic_def, abi_member_head_size_def] >>
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
    !mem. val_in_memory tv (EL i vs) (sb+32+i*type_memory_size tv) mem ==>
      abi_encoder_open_input ei ct rv (sb+32+i*type_memory_size tv)
        (type_memory_size tv) mem` by
    (rpt strip_tac >> first_assum irule >> simp[] >>
     qexists_tac `mem0` >> simp[arithmeticTheory.ADD_ASSOC]) >>
  qpat_x_assum `!i. _ ==> ?rv. _` mp_tac >>
  CONV_TAC (LAND_CONV (BINDER_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_IMP_THM)))) >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV SKOLEM_THM)) >>
  disch_then (qx_choose_then `f` assume_tac) >>
  qexists_tac `ListV (GENLIST f (LENGTH vs))` >> conj_tac
  >- (`enc (Array NONE ct) (ListV (GENLIST f (LENGTH vs))) =
       enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
        (irule abi_encoder_dynamic_array_encoding_cong >> simp[]) >>
      gvs[Once enc_def]) >>
  rpt strip_tac >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_dynamic_source >>
  simp[value_has_type_def, Once vyper_to_abi_def] >> strip_tac >>
  qpat_x_assum `!t env' av'. _`
    (qspecl_then [`ty`, `env`, `ListV avs`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  irule abiEncoderOpenInputTheory.open_array >> simp[abi_member_head_size_def] >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >> fs[type_slot_size_def] >>
  `n <= n * type_slot_size tv` by (simp[arithmeticTheory.LE_MULT_LCANCEL]) >> decide_tac
QED
Resume abi_encoder_uniform_value_source[tuple]:
  rpt strip_tac >>
  drule_all uniform_list_ih_members >> strip_tac >>
  pop_assum (mk_asm "members") >>
  drule source_reps_any_dynamic >> strip_tac >>
  drule source_reps_tuple_head >> strip_tac >>
  qexists_tac `Tuple cts` >> simp[vyper_to_abi_type_def] >> rpt strip_tac >>
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
Resume abi_encoder_uniform_value_source[sarray]:
  rpt strip_tac >> drule_all uniform_list_ih_members >> strip_tac >>
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
Resume abi_encoder_uniform_value_source[struct]:
  rpt strip_tac >> drule_all uniform_list_ih_members >> strip_tac >>
  pop_assum (mk_asm "members") >>
  drule source_reps_any_dynamic >> strip_tac >>
  drule source_reps_tuple_head >> strip_tac >>
  qexists_tac `Tuple cts` >> simp[vyper_to_abi_type_def] >> rpt strip_tac >>
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

Finalise abi_encoder_uniform_value_source
