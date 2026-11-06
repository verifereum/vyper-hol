(* Aggregate constructors at the actual descending struct map, with fixed layout. *)
Theory entryReachBodyDescendingAggregateClosure
Ancestors
  entryReachBodyDescendingMembers entryReachBodyDescendingProducer
  entryReachBodyDescendingMetadata entryReachBodyCanonicalMembers
  entryReachBodyCanonicalArrayChild calldataRecursiveProducers
  abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract abiDecoderMemberInfos
  valueEncodingProps valueEncoding vyperABI vyperTyping vyperValue contractABI
  exprLowering compileEnv abiEncoder abiDecoderFixedInputs abiDecoderFixedMemory
  list rich_list valueEncodingProofs abiCanonicalHeadSize abiDecoderStruct
  valueEncodingTyping abiStaticDynarrayLayout

Theorem descending_tuple_values[local]:
  entry_descending_metadata ce env sf (TupleT tys) (TupleTV tvs) di av v ==>
  ?avs vs. av = ListV avs /\ v = ArrayV (TupleV vs)
Proof
  Cases_on `av` >> simp_tac bool_ss [entry_descending_metadata_def] >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, Once has_type_def, Once abi_to_vyper_def,
      AllCaseEqs()]
QED

Theorem descending_complex_tuple_result[local]:
  (last.cs_current_insts = [] ==> !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  entry_descending_members ce env sf tys tvs avs vs /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ce env sf
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent ambient b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) st s /\
  sb+LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d+SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN ambient /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET ambient /\
  type_memory_size (TupleTV tvs) = SUM (MAP (type_memory_bytes ce) tys) ==>
  ?t. array_child_result ctx fn oid root extent ambient
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
    b cap site limit_st st last d (TupleTV tvs) (ArrayV (TupleV vs)) s t
Proof
  strip_tac >>
  `?t. canonical_members_effect ctx fn ambient d (SUM (MAP (type_memory_bytes ce) tys)) st s t /\
    canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) last t /\
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) tys))] s t` by
    (irule (entry_descending_certified_local_complex_endpoint |> Q.INST
      [`cert` |-> `\z. z.cs_current_insts = [] ==> !bb.
        lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0`] |> SIMP_RULE bool_ss []) >>
     asm_rewrite_tac[] >> conj_tac
     >- metis_tac[calldata_member_tail_empty_exit_phi] >>
     qexistsl_tac [`avs`,`dyn`,`env`,`sf`] >> asm_rewrite_tac[]) >>
  qexists_tac `t` >>
  gvs[canonical_members_effect_def, canonical_members_frame_def,
      array_child_result_def, val_in_memory_tuple, Excl "enc_def"]
QED

Theorem entry_descending_tuple_producer:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  (!i av v. i < LENGTH tys ==> entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (EL i tys) (EL i tvs) av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (TupleT tys) (TupleTV tvs) pav pv ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_descending_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >> rename1 `fn_has_code st last fn` >>
  drule descending_tuple_values >> strip_tac >> gvs[Excl "enc_def"] >>
  `abi_decoder_metadata ce env (TupleT tys) (TupleTV tvs)
    (type_to_abi_dec_info ce.ce_struct_fields ce (TupleT tys)) (ListV avs) (ArrayV (TupleV vs))` by
    metis_tac[entry_descending_metadata_transport] >>
  drule_all abi_decoder_tuple_members >>
  simp_tac bool_ss [GSYM entry_descending_members_equiv] >> disch_tac >>
  `type_memory_size (TupleTV tvs) = SUM (MAP (type_memory_bytes ce) tys)` by
    (qpat_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_coherent_tuple_iff] >> strip_tac >> gvs[] >>
     drule abi_decoder_member_infos_layout >> simp[type_memory_size_def]) >>
  `canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell (SUM (MAP (type_memory_bytes ce) tys)) st s` by
    (simp[canonical_members_frame_def] >> gvs[Excl "enc_def"]) >>
  `cell+SUM (MAP (type_memory_bytes ce) tys) < dimword (:256)` by gvs[Excl "enc_def"] >>
  `compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
      (abi_decoder_member_infos sf ce tys)) st = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decoder_tuple_infos]) >>
  `(!i. i < LENGTH tys ==> entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
      ctx fn oid root extent ambient b cap site limit_st)` by simp[] >>
  fs[vyper_to_abi_types_MAP, Excl "enc_def"] >>
  irule descending_complex_tuple_result >> asm_rewrite_tac[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`dst`,`EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`,`sb`,`src`] >>
  simp[Excl "enc_def"]
QED

Theorem descending_fixed_result[local]:
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    st last d (TupleTV (REPLICATE n tv)) (ArrayV (TupleV vs)) s t /\ LENGTH vs = n ==>
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    st last d (ArrayTV tv (Fixed n))
      (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) s t
Proof
  simp[array_child_result_def, type_memory_size_def, type_memory_size_list_sum,
       map_replicate, SUM_REPLICATE, val_in_memory_tuple] >> strip_tac >>
  asm_rewrite_tac[] >> irule abi_decoder_fixed_array_memory >> simp[]
QED

Theorem entry_descending_fixed_array_producer:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  (!av v. entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) pav pv
      ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_descending_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >> rename1 `fn_has_code st last fn` >>
  `abi_decoder_metadata ce env (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Fixed n))) pav pv` by
    metis_tac[entry_descending_metadata_transport] >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  qpat_x_assum `pav = _` SUBST_ALL_TAC >> qpat_x_assum `pv = _` SUBST_ALL_TAC >>
  `type_memory_size (ArrayTV tv (Fixed n)) = type_memory_bytes ce (ArrayT ty (Fixed n))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) =
    SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))` by
    simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  `canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell (SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))) st s` by
    (simp[canonical_members_frame_def] >> gvs[Excl "enc_def"]) >>
  `type_memory_size (TupleTV (REPLICATE n tv)) =
    SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))` by
    gvs[type_memory_size_def, type_memory_size_list_sum, map_replicate, SUM_REPLICATE] >>
  `?t. array_child_result ctx fn oid root extent ambient
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
    b cap site limit_st st last cell (TupleTV (REPLICATE n tv)) (ArrayV (TupleV vs)) s t` by
    (irule descending_complex_tuple_result >> asm_rewrite_tac[] >>
     qexistsl_tac [`avs`,`ce`,`dst`,`is_abi_dynamic ce.ce_struct_fields ty`,`env`,`sb`,`sf`,`src`,
       `REPLICATE n ty`] >>
     gvs[GSYM entry_descending_members_equiv, abi_decoder_fixed_array_infos,
       Once vyper_to_abi_type_def, canonical_array_tuple, map_replicate,
       EL_REPLICATE, Excl "enc_def"]) >>
  qexists_tac `t` >> irule descending_fixed_result >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem descending_struct_result[local]:
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    st last d (TupleTV tvs) (ArrayV (TupleV (MAP SND fields))) s t /\
  LENGTH names = LENGTH tvs /\ value_has_type (StructTV (ZIP (names,tvs))) (StructV fields) ==>
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    st last d (StructTV (ZIP (names,tvs))) (StructV fields) s t
Proof
  simp[array_child_result_def, type_memory_size_def, val_in_memory_tuple,
    val_in_memory_struct] >> strip_tac >>
  `type_memory_size_fields (ZIP (names,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  asm_rewrite_tac[] >> irule static_fields_memory_zip >>
  gvs[Once value_has_type_def]
QED

Theorem entry_descending_struct_producer:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  abi_decoder_coherent ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) /\
  (!i av v. i < LENGTH args ==> entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce (env \\ nsid) (sf \\ nsid_to_string nsid) (EL i (MAP SND args)) (EL i tvs) av v
      ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) pav pv
      ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_descending_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >> rename1 `fn_has_code st last fn` >>
  `abi_decoder_metadata ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    (type_to_abi_dec_info ce.ce_struct_fields ce (StructT nsid)) pav pv` by
    metis_tac[entry_descending_metadata_transport] >>
  `abi_to_vyper env (StructT nsid) pav = SOME pv` by fs[abi_decoder_metadata_def] >>
  drule abi_decoder_struct_values >> strip_tac >>
  qpat_x_assum `pav = _` SUBST_ALL_TAC >> qpat_x_assum `pv = _` SUBST_ALL_TAC >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  drule abi_decoder_struct_infos >> disch_tac >> fs[Excl "enc_def"] >>
  `entry_descending_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (MAP SND args) tvs avs (MAP SND fields)` by simp[entry_descending_members_equiv] >>
  `type_memory_size_list tvs = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    (drule abi_decoder_members_relations >> strip_tac >>
     drule abi_decoder_member_infos_layout >> simp[]) >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `canonical_members_frame ctx fn oid root extent ambient b cap site limit_st dst src sb cell
    (SUM (MAP (type_memory_bytes ce) (MAP SND args))) st s` by
    (simp[canonical_members_frame_def] >> gvs[type_memory_size_def, Excl "enc_def"]) >>
  `?t. array_child_result ctx fn oid root extent ambient
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
    b cap site limit_st st last cell (TupleTV tvs) (ArrayV (TupleV (MAP SND fields))) s t` by
    (irule descending_complex_tuple_result >> asm_rewrite_tac[] >>
     qexistsl_tac [`avs`,`ce`,`dst`,`EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args)`,
       `env \\ nsid`,`sb`,`sf \\ nsid_to_string nsid`,`src`,`MAP SND args`] >>
     gvs[abi_decoder_struct_infos, Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
       type_memory_size_def, Excl "enc_def"]) >>
  qexists_tac `t` >> irule descending_struct_result >>
  goal_assum (drule_at Any) >> simp[] >> fs[abi_decoder_metadata_def]
QED
