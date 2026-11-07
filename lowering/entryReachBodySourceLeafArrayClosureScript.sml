(* Source producer closure for scalars and dynamic arrays. *)
Theory entryReachBodySourceLeafArrayClosure
Ancestors
  entryReachBodySourceProducer entryReachBodyDescendingScalarClosure
  entryReachBodySourceMemberEntry
  entryReachBodySourceBulkEndpoint entryReachBodySourceNonbulkConstructor
  entryReachBodyConversionSupport supportedTypes abiDecoderCoherence
  abiDecoderTypedContract exprLowering compileEnv vyperABI vyperTyping
  valueEncoding vyperValue contractABI entryReachBodyCanonicalArrayChild

Theorem entry_source_base_producer:
  abi_decoder_coherent ce env sf (BaseT bt) tv ==>
  entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (BaseT bt) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> Cases_on `supported_scalar_type (BaseT bt)`
  >- (irule entry_source_scalar_producer_bridge >> simp[] >>
      irule entry_descending_base_producer >> simp[]) >>
  simp_tac bool_ss [entry_source_certified_child_producer_def,
    entry_source_metadata_def] >>
  rpt strip_tac >> qpat_x_assum `entry_abi_support _ _` mp_tac >>
  once_rewrite_tac[entry_abi_support_cases] >> simp[]
QED

Theorem entry_source_flag_producer:
  entry_source_certified_child_producer cert ce env sf (FlagT nsid) tv av v
    ctx fn oid root extent ambient b cap site limit_st
Proof
  simp[entry_source_certified_child_producer_def,
    entry_source_flag_metadata_excluded]
QED

Theorem entry_source_dynamic_producer:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) /\
  (!av v. entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) pav pv
      ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_source_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >> rename1 `fn_has_code st last fn` >>
  `?xs. pv = ArrayV (DynArrayV xs)` by
    (qpat_assum `entry_source_metadata _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [entry_source_metadata_def] >> strip_tac >>
     Cases_on `pv` >> gvs[value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV a)` >> Cases_on `a` >>
     gvs[value_has_type_def]) >>
  `?avs. pav = ListV avs` by
    (gvs[entry_source_metadata_def, Once vyper_to_abi_def,
         AllCaseEqs(), Excl "enc_def"] >> metis_tac[]) >>
  gvs[Excl "enc_def"] >>
  `type_memory_size (ArrayTV tv (Dynamic n)) =
    type_memory_bytes ce (ArrayT ty (Dynamic n))` by
    fs[entry_source_metadata_def, Excl "enc_def"] >>
  `entry_owned_region oid root extent cell
    (type_memory_bytes ce (ArrayT ty (Dynamic n))) s` by gvs[] >>
  `cell+type_memory_bytes ce (ArrayT ty (Dynamic n)) < dimword (:256)` by gvs[] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- suspend "nonbulk"
  >> suspend "bulk"
QED
Resume entry_source_dynamic_producer[nonbulk]:
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) n` by simp[Once type_to_abi_dec_info_def] >>
  irule entry_source_nonbulk_array_constructor >>
  qpat_assum `entry_source_metadata _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[Excl "enc_def", GSYM vyper_to_abi_type_def] >>
  goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
  qexists_tac `sb` >> simp[Excl "enc_def"] >> decide_tac
QED
Resume entry_source_dynamic_producer[bulk]:
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
  drule_all entry_source_bulk_owned_endpoint >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >> simp[array_child_result_def] >> gvs[Excl "enc_def"]
QED
Finalise entry_source_dynamic_producer
