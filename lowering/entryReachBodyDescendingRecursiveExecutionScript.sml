(* Recursive canonical execution, conditional on an installed no-PHI exit. *)
Theory entryReachBodyDescendingRecursiveExecution
Ancestors
  entryReachBodyDescendingScalarClosure entryReachBodyDescendingAggregateClosure
  entryReachBodyDescendingDynamic entryReachBodyDescendingProducer
  entryReachBodyDescendingMetadata entryReachBodyCanonicalBulkEndpoint
  entryReachBodyConditionalProducer entryReachBodyCertifiedProducer
  abiDecoderCoherence abiDecoderTypedContract exprLowering compileEnv
  valueEncoding vyperABI vyperValue contractABI list abiDecoderCorrectPrimitiveArray
  entryReachBodyCanonicalArrayChild

Theorem descending_dynamic_producer[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) /\
  (!av v. entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) pav pv
      ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_descending_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >> rename1 `fn_has_code st last fn` >>
  `type_memory_size (ArrayTV tv (Dynamic n)) = type_memory_bytes ce (ArrayT ty (Dynamic n))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `abi_decoder_metadata ce env (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic n))) pav pv` by
    (fs[entry_descending_metadata_transport]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gvs[Excl "enc_def"] >>
  `entry_owned_region oid root extent cell (type_memory_bytes ce (ArrayT ty (Dynamic n))) s` by gvs[] >>
  `cell+type_memory_bytes ce (ArrayT ty (Dynamic n)) < dimword (:256)` by gvs[] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- suspend "nonbulk"
  >> suspend "bulk"
QED
Resume descending_dynamic_producer[nonbulk]:
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) n` by simp[Once type_to_abi_dec_info_def] >>
  irule entry_descending_nonbulk_array_constructor >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[Excl "enc_def", GSYM vyper_to_abi_type_def] >>
  goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
  qexists_tac `sb` >> simp[Excl "enc_def"] >> decide_tac
QED
Resume descending_dynamic_producer[bulk]:
  `~is_abi_dynamic ce.ce_struct_fields ty /\
   ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by fs[] >>
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) F n` by
    simp[Once type_to_abi_dec_info_def] >>
  qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  `mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic n))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (ArrayT ty (Dynamic n))) (ListV avs)` by
    simp[Excl "enc_def"] >>
  `sb+LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic n))) (ListV avs)) < dimword (:256)` by
    simp[Excl "enc_def"] >>
  drule_all entry_canonical_bulk_owned_endpoint >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >> simp[array_child_result_def] >> gvs[Excl "enc_def"]
QED
Finalise descending_dynamic_producer

Theorem descending_certified_producer_induction[local]:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  abi_decoder_coherent ce env sf ty tv /\
  !av v ctx fn oid root extent ambient b cap site limit_st.
    entry_descending_certified_child_producer
      (\z. z.cs_current_insts = [] ==> !bb.
        lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
      ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      conj_asm1_tac >- simp[abi_decoder_coherent_base_iff] >>
      rpt gen_tac >> irule entry_descending_base_producer >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      conj_asm1_tac >- simp[abi_decoder_coherent_flag_iff] >>
      rpt gen_tac >> irule entry_descending_flag_producer >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      conj_asm1_tac >- simp[abi_decoder_coherent_array_iff] >>
      rpt gen_tac >> Cases_on `bound`
      >- (irule entry_descending_fixed_array_producer >> simp[])
      >> irule descending_dynamic_producer >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      fs[LIST_REL_EL_EQN] >>
      conj_asm1_tac
      >- (simp[abi_decoder_coherent_tuple_iff, LIST_REL_EL_EQN]) >>
      rpt gen_tac >> irule entry_descending_tuple_producer >> simp[])
  >> rpt gen_tac >> strip_tac >> fs[LIST_REL_EL_EQN] >>
  conj_asm1_tac
  >- (simp[abi_decoder_coherent_struct_iff] >>
      qexists_tac `tvs` >> simp[LIST_REL_EL_EQN]) >>
  rpt gen_tac >> irule entry_descending_struct_producer >> simp[]
QED

Theorem entry_descending_certified_producer_exists:
  abi_decoder_coherent ce env sf ty tv ==>
  entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  metis_tac[descending_certified_producer_induction]
QED

Theorem entry_canonical_certified_producer_exists:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv ==>
  entry_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [GSYM entry_descending_certified_child_root] >>
  strip_tac >> irule entry_descending_certified_producer_exists >> simp[]
QED
