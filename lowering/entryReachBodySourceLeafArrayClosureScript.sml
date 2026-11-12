(* Source producer closure for scalars and dynamic arrays. *)
Theory entryReachBodySourceLeafArrayClosure
Ancestors
  valueEncodingDefs entryReachBodySourceProducer entryReachBodyDescendingScalarClosure entryReachBodyCanonicalWordEndpoint entryReachBodyCanonicalBytesEndpoint abiDecoderWordTyped abiDecoderBytestring abiDecoderBytesTyped abiEncoder abiDecoderBytes abiDecoderLayout valueEncodingProps words entryReachBodyDescendingMetadata
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

(* Local notation only: the proposition has no new HOL constant. *)
val _ = temp_overload_on ("source_child_gas", ``
  \cert ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st.
  !st last dst src sb cell s.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) st = ((),last) /\
    abi_decoder_coherent ce env sf ty tv /\
    entry_source_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v /\
    mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
      (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av /\
    sb+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    cell+type_memory_size tv < dimword (:256) /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w cell) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    fn_has_code st last fn /\ abi_decoder_code st last /\ cert last /\
    fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
    oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
    window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET ambient /\
    oid NOTIN ambient /\ entry_scratch_ready ambient b cap s /\ alloca_inv s /\
    abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
    entry_owned_region oid root extent cell (type_memory_size tv) s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. array_child_result ctx fn oid root extent ambient
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      b cap site limit_st st last cell tv v s t /\ gas_path ctx fn s 0 (OK t)``);

Theorem entry_source_flag_producer_gas:
  source_child_gas cert ce env sf (FlagT nsid) tv av v
    ctx fn oid root extent ambient b cap site limit_st
Proof
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  simp[entry_source_flag_metadata_excluded]
QED

Theorem entry_source_dynamic_producer_gas:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) /\
  (!av v. source_child_gas
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st) ==>
  source_child_gas
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) pav pv
      ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
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
Resume entry_source_dynamic_producer_gas[nonbulk]:
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) n` by simp[Once type_to_abi_dec_info_def] >>
  irule entry_source_nonbulk_array_constructor_gas >>
  qpat_assum `entry_source_metadata _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[Excl "enc_def", GSYM vyper_to_abi_type_def] >>
  goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
  metis_tac[]
QED
Resume entry_source_dynamic_producer_gas[bulk]:
  `~is_abi_dynamic ce.ce_struct_fields ty /\
   ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by gvs[] >>
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
  drule_all entry_source_bulk_owned_endpoint_gas >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >> simp[array_child_result_def] >> gvs[Excl "enc_def"]
QED
Finalise entry_source_dynamic_producer_gas

Theorem source_base_metadata[local]:
  supported_scalar_type (BaseT bt) /\
  entry_source_metadata ce env (sf :string |-> (string # vyperAST$type # num) list) (BaseT bt) tv di av v ==>
  abi_decoder_metadata ce env (BaseT bt) tv di av v
Proof
  strip_tac >> drule_all entry_source_scalar_metadata >>
  Cases_on `bt` >>
  simp[entry_descending_metadata_def, abi_decoder_metadata_def,
       type_to_abi_dec_info_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def]
QED

Theorem source_word_producer_gas[local]:
  supported_scalar_type (BaseT bt) /\
  abi_decoder_coherent ce env sf (BaseT bt) tv /\
  type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp ==>
  source_child_gas cert ce env sf (BaseT bt) tv av v
    ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt gen_tac >> strip_tac >>
  `abi_decoder_metadata ce env (BaseT bt) tv
    (type_to_abi_dec_info sf ce (BaseT bt)) av v` by
    (irule source_base_metadata >> asm_rewrite_tac[] >>
     qexists_tac `sf` >> gvs[]) >>
  `type_memory_size tv = type_memory_bytes ce (BaseT bt)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_memory_bytes ce (BaseT bt) = 32 /\ ~is_abi_dynamic ce.ce_struct_fields (BaseT bt)` by
    (drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >> simp[]) >>
  `LENGTH (enc (vyper_to_abi_type env (BaseT bt)) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `sb < dimword (:256) /\ cell < dimword (:256)` by decide_tac >>
  `compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `abi_decoder_metadata ce env (BaseT bt) tv (DecPrimWord clamp) av v` by gvs[] >>
  `mem_bytes_at sb 32 (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (BaseT bt)) av` by gvs[] >>
  `entry_owned_region oid root extent cell (type_memory_bytes ce (BaseT bt)) s` by gvs[] >>
  drule_all entry_canonical_word_owned_endpoint_gas >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >> simp[array_child_result_def] >> gvs[]
QED

Theorem source_bytes_producer_gas[local]:
  supported_scalar_type (BaseT bt) /\
  abi_decoder_coherent ce env sf (BaseT bt) tv /\
  type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n ==>
  source_child_gas cert ce env sf (BaseT bt) tv av v
    ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt gen_tac >> strip_tac >>
  `abi_decoder_metadata ce env (BaseT bt) tv
    (type_to_abi_dec_info sf ce (BaseT bt)) av v` by
    (irule source_base_metadata >> asm_rewrite_tac[] >>
     qexists_tac `sf` >> gvs[]) >>
  `type_memory_size tv = type_memory_bytes ce (BaseT bt)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_memory_bytes ce (BaseT bt) = abi_decode_bytes_copy_size n /\
   n + 32 <= abi_decode_bytes_copy_size n` by
    (drule abi_decoder_bytestring_cases >> disch_then (qspec_then `n` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >>
     metis_tac[abi_decoder_bytes_copy_size, type_memory_bytes_def]) >>
  `n < dimword (:256) /\ cell+abi_decode_bytes_copy_size n < dimword (:256)` by
    (gvs[] >> decide_tac) >>
  `compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `abi_decoder_metadata ce env (BaseT bt) tv (DecBytestring n) av v` by gvs[] >>
  `entry_owned_region oid root extent cell (type_memory_bytes ce (BaseT bt)) s` by gvs[] >>
  drule_all entry_canonical_bytes_owned_endpoint_gas >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >> simp[array_child_result_def] >> gvs[]
QED

Theorem entry_source_base_producer_gas:
  abi_decoder_coherent ce env sf (BaseT bt) tv ==>
  source_child_gas cert ce env sf (BaseT bt) tv av v
    ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  Cases_on `supported_scalar_type (BaseT bt)`
  >- (Cases_on `bt`
      >~ [`BaseT (BytesT bound)`] >-
        (Cases_on `bound`
         >- (match_mp_tac (Q.GEN `clamp` source_word_producer_gas) >> simp[Once type_to_abi_dec_info_def] >>
             goal_assum (drule_at Any) >> simp[]) >>
         match_mp_tac (Q.GEN `n` source_bytes_producer_gas) >> simp[Once type_to_abi_dec_info_def] >>
         goal_assum (drule_at Any) >> simp[])
      >~ [`BaseT (StringT n)`] >-
        (match_mp_tac (Q.GEN `n` source_bytes_producer_gas) >> simp[Once type_to_abi_dec_info_def] >>
         goal_assum (drule_at Any) >> simp[]) >>
      match_mp_tac (Q.GEN `clamp` source_word_producer_gas) >> simp[Once type_to_abi_dec_info_def] >>
      goal_assum (drule_at Any) >> simp[]) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  simp_tac bool_ss [entry_source_metadata_def] >>
  rpt strip_tac >> qpat_x_assum `entry_abi_support _ _` mp_tac >>
  once_rewrite_tac[entry_abi_support_cases] >> simp[]
QED
