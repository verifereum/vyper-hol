Theory bodyFullAbiDecodeMemberLayout
Ancestors
  calldataRecursiveProducers tupleMemoryLayout typedCopyTuplePtr
  exprSimPopNestedLocalLayout placeMemoryTypedBase valueEncodingTyping memoryValueEncoding
  valueEncodingProofs vyperTypeDefaults vyperTyping finite_map alist list rich_list
  arithmetic abiDecoderCoherence abiDecoderMemberInfos exprLowering valueEncodingDefs

(* The typed slot observations suffice to transport the aggregate observation. *)
val member_memory_transport = ``\tv tvs.
  !d mem mem'.
    (!k v. k < LENGTH tvs /\ value_has_type (EL k tvs) v /\
       val_in_memory (EL k tvs) v (d+SUM (TAKE k (MAP type_memory_size tvs))) mem ==>
       val_in_memory (EL k tvs) v (d+SUM (TAKE k (MAP type_memory_size tvs))) mem') ==>
    !v. value_has_type tv v /\ val_in_memory tv v d mem ==>
        val_in_memory tv v d mem'``;

Theorem member_tuple_memory_transport[local]:
  values_have_types tvs vs /\ tuple_in_memory vs tvs d mem /\
  (!k v. k < LENGTH tvs /\ value_has_type (EL k tvs) v /\
    val_in_memory (EL k tvs) v (d+SUM (TAKE k (MAP type_memory_size tvs))) mem ==>
    val_in_memory (EL k tvs) v (d+SUM (TAKE k (MAP type_memory_size tvs))) mem') ==>
  tuple_in_memory vs tvs d mem'
Proof
  simp[values_have_types_LIST_REL, LIST_REL_EL_EQN] >> strip_tac >>
  irule tuple_in_memory_from_elements >> simp[] >> rpt strip_tac >>
  `i < LENGTH tvs` by decide_tac >>
  `val_in_memory (EL i tvs) (EL i vs)
     (d+SUM (MAP type_memory_size (TAKE i tvs))) mem` by
    (irule tuple_in_memory_element >> simp[]) >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (qpat_assum `!n. n < LENGTH tvs ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  rewrite_tac[MAP_TAKE] >>
  qpat_assum `!k v. k < LENGTH tvs /\ _ /\ val_in_memory _ _ _ mem ==> _`
    (qspecl_then [`i`, `EL i vs`] irule) >> fs[MAP_TAKE]
QED

Theorem member_fixed_memory_transport[local]:
  evaluate_type env ty = SOME tv ==>
  (^member_memory_transport) (ArrayTV tv (Fixed n)) (REPLICATE n tv)
Proof
  simp[] >> strip_tac >> rpt gen_tac >> strip_tac >> qx_gen_tac `av` >>
  Cases_on `av` >> simp[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> simp[value_has_type_def] >>
  rpt strip_tac >> rename1 `sparse_has_type tv n kvs` >>
  `!j x. MEM (j,x) kvs ==> j < n` by metis_tac[typed_sparse_entry] >>
  drule_all sarray_memory_index >> disch_then (fn th =>
    qpat_x_assum `val_in_memory (ArrayTV tv (Fixed n)) _ d mem`
      (assume_tac o REWRITE_RULE[th]) >>
    rewrite_tac[th]) >>
  qx_gen_tac `i` >> strip_tac >>
  `value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs))` by
    simp[value_has_type_def] >>
  drule_all typed_memory_sparse_lookup_type >> disch_then (qspec_then `i` assume_tac) >>
  qpat_x_assum `!k v. k < n /\ _ ==> _` (qspecl_then
    [`i`, `case ALOOKUP kvs i of NONE => default_value tv | SOME x => x`] mp_tac) >>
  simp[EL_REPLICATE, REPLICATE_GENLIST, TAKE_GENLIST,
       arithmeticTheory.MIN_DEF] >>
  rewrite_tac[GSYM REPLICATE_GENLIST, SUM_REPLICATE] >>
  qpat_assum `!j. j < n ==> val_in_memory _ _ _ mem`
    (qspec_then `i` mp_tac) >> simp[]
QED

Theorem abi_decode_typed_member_layout:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex dyn infos ==>
  ?env1 sf1 tys1 tvs1.
    infos = abi_decoder_member_infos sf1 ce tys1 /\
    LIST_REL (abi_decoder_coherent ce env1 sf1) tys1 tvs1 /\
    (^member_memory_transport) tv tvs1
Proof
  Cases_on `ty`
  >- (Cases_on `b` >> simp[type_to_abi_dec_info_def] >>
      Cases_on `b'` >> simp[type_to_abi_dec_info_def])
  >- (strip_tac >> drule calldata_tuple_member_metadata >> strip_tac >>
      qexistsl_tac [`env`, `sf`, `l`, `tvs`] >> gvs[] >>
      rpt gen_tac >> strip_tac >> qx_gen_tac `v` >>
      Cases_on `v` >> simp[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      simp[value_has_type_def, val_in_memory_def] >>
      metis_tac[member_tuple_memory_transport])
  >- (Cases_on `b` >- (
        (strip_tac >> drule calldata_fixed_member_metadata >> strip_tac >>
        qexistsl_tac [`env`, `sf`, `REPLICATE n t`, `REPLICATE n tv'`] >>
        `evaluate_type env t = SOME tv'` by
          (qpat_assum `abi_decoder_coherent ce env sf t tv'`
             (mp_tac o MATCH_MP abi_decoder_coherent_header) >> simp[abi_decoder_header_def]) >>
        drule (BETA_RULE member_fixed_memory_transport) >>
        disch_then (qspec_then `n` mp_tac) >> gvs[EL_REPLICATE] >> (metis_tac[abi_decoder_header_def, EL_REPLICATE, calldata_fixed_member_metadata, BETA_RULE member_fixed_memory_transport]))) >>
      simp[type_to_abi_dec_info_def])
  >- (strip_tac >> drule calldata_struct_member_metadata >> strip_tac >>
      qexistsl_tac [`env \\ p`, `sf \\ nsid_to_string p`, `MAP SND args`, `tvs`] >>
      gvs[] >> rpt gen_tac >> strip_tac >> qx_gen_tac `v` >>
      Cases_on `v` >> simp[value_has_type_def, val_in_memory_def] >>
      simp[fields_in_memory_tuple, MAP_ZIP] >> strip_tac >>
      `values_have_types tvs (MAP SND l)` by
        (drule struct_has_type_values_have_types >> simp[MAP_ZIP]) >>
      metis_tac[member_tuple_memory_transport]) >>
  simp[type_to_abi_dec_info_def]
QED

Theorem abi_decode_member_memory_sum:
  !tys. FOLDR (\(_,_,msz) acc. msz+acc) 0 (abi_decoder_member_infos sf ce tys) =
        SUM (MAP (type_memory_bytes ce) tys)
Proof
  Induct >> simp[abi_decoder_member_infos_def] >>
  gvs[abi_decoder_member_infos_def]
QED
