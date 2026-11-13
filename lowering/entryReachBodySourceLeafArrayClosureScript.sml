(* Source producer closure for scalars and dynamic arrays. *)
Theory entryReachBodySourceLeafArrayClosure
Ancestors
  valueEncodingDefs entryReachBodySourceProducer entryReachBodyDescendingScalarClosure
  entryReachBodySourceMemberEntry
  entryReachBodySourceBulkEndpoint entryReachBodySourceNonbulkConstructor
  entryReachBodyConversionSupport supportedTypes abiDecoderCoherence
  abiDecoderTypedContract exprLowering compileEnv vyperABI vyperTyping
  valueEncoding vyperValue contractABI entryReachBodyCanonicalArrayChild
  entryReachBodyCanonicalWordEndpoint abiCanonicalHeadSize abiStaticAggregateProps
  valueEncodingProofs abiDecoderClamp

(* bytes0 has no ABI type (valid_bytes_bound (SOME 0) fails), so it bypasses
   the typed metadata: its source value encodes as a zero word, which passes
   the clamp and lays out the empty value. *)
Theorem entry_source_bytes0_producer:
  entry_source_certified_child_producer cert ce env sf (BaseT (BytesT (Fixed 0))) tv av v
    ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [entry_source_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `entry_source_metadata _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_source_metadata_def]) >>
  gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_def, vyper_to_abi_base_def,
      vyper_to_abi_type_def, vyper_base_to_abi_type_def, type_memory_size_def] >>
  `type_to_abi_dec_info sf ce (BaseT (BytesT (Fixed 0))) = DecPrimWord (BytesMClamp 0)` by
    simp[Once type_to_abi_dec_info_def, type_to_abi_clamp_def] >>
  `compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
     (DecPrimWord (BytesMClamp 0)) st = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `entry_owned_region oid root extent cell
     (type_memory_bytes ce (BaseT (BytesT (Fixed 0)))) s` by simp[type_memory_bytes_def] >>
  `sb < dimword (:256) /\ cell < dimword (:256)` by decide_tac >>
  `abi_decoder_clamp_valid (BytesMClamp 0)
     (abi_decode_load CALLDATALOAD (n2w sb : bytes32) s)` by
    simp[abi_decode_load_bytes, word_of_bytes_replicate_zero, abi_decoder_clamp_valid_def,
         wordsTheory.ZERO_SHIFT] >>
  `!mem. mem_bytes_at cell 32 mem = mem_bytes_at sb 32 (abi_decode_source CALLDATALOAD s) ==>
     val_in_memory (BaseTV (BytesT (Fixed 0))) (vyperValue$BytesV []) cell mem` by
    (rpt strip_tac >> irule abi_static_primitive_layout >>
     simp[is_word_type_def, value_has_type_def, vyper_to_abi_base_def,
          vyper_base_to_abi_type_def]) >>
  drule_all entry_canonical_word_memory_endpoint >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >>
  gvs[array_child_result_def, type_memory_size_def, type_memory_bytes_def]
QED

Theorem entry_source_base_producer:
  abi_decoder_coherent ce env sf (BaseT bt) tv ==>
  entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (BaseT bt) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> Cases_on `bt = BytesT (Fixed 0)`
  >- (gvs[] >> irule entry_source_bytes0_producer) >>
  Cases_on `entry_abi_leaf (BaseT bt)`
  >- (irule entry_source_scalar_producer_bridge >> simp[] >>
      irule entry_descending_base_producer >> simp[]) >>
  simp_tac bool_ss [entry_source_certified_child_producer_def,
    entry_source_metadata_def] >>
  rpt strip_tac >> qpat_x_assum `entry_abi_support _ _` mp_tac >>
  once_rewrite_tac[entry_abi_support_cases] >> simp[]
QED

Theorem entry_source_flag_producer:
  entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (FlagT nsid) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  Cases_on `abi_decoder_coherent ce env sf (FlagT nsid) tv`
  >- (irule entry_source_scalar_producer_bridge >> simp[entry_abi_leaf_def] >>
      irule entry_descending_flag_producer >> simp[]) >>
  simp[entry_source_certified_child_producer_def]
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
  qpat_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` (irule_at Any) >>
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
