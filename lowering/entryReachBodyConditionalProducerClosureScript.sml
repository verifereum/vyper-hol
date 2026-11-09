(* Scalar and array closure of the conditional owned decoder producer. *)
Theory entryReachBodyConditionalProducerClosure
Ancestors
  valueEncodingDefs entryReachBodyConditionalProducer entryReachBodyCanonicalWordEndpoint
  entryReachBodyCanonicalBytesEndpoint entryReachBodyConditionalMembers
  entryReachBodyConditionalArrayConstructor entryReachBodyCanonicalBulkEndpoint
  abiDecoderCoherence abiDecoderWordTyped abiDecoderLayout abiDecoderTypedContract
  entryReachBodyCanonicalArrayChild entryReachBodyCanonicalMembers abiDecoderBytestring abiDecoderBytestringCases abiDecoderBytesTyped
  compileEnv exprLowering abiEncoder abiDecoderBytes valueEncoding vyperTyping words vfmConstants
  abiDecoderCorrectPrimitiveArray vyperABI

Theorem conditional_word_producer[local]:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp ==>
  entry_conditional_array_child_producer ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_conditional_array_child_producer_def] >>
  rpt gen_tac >> strip_tac >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_memory_bytes ce ty = 32 /\ ~is_abi_dynamic ce.ce_struct_fields ty` by
    (drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >> simp[]) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `sb < dimword (:256) /\ cell < dimword (:256)` by decide_tac >>
  `compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >> simp[]) >>
  `abi_decoder_metadata ce env ty tv (DecPrimWord clamp) av v` by
    (qpat_x_assum `abi_decoder_metadata _ _ _ _ _ _ _` mp_tac >> simp[]) >>
  `mem_bytes_at sb 32 (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av` by fs[] >>
  `entry_owned_region oid root extent cell (type_memory_bytes ce ty) s` by fs[] >>
  drule_all entry_canonical_word_owned_endpoint >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >> simp[array_child_result_def] >> gvs[]
QED

Theorem conditional_bytes_producer[local]:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  type_to_abi_dec_info ce.ce_struct_fields ce ty = DecBytestring n ==>
  entry_conditional_array_child_producer ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_conditional_array_child_producer_def] >>
  rpt gen_tac >> strip_tac >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
   n + 32 <= abi_decode_bytes_copy_size n` by
    (drule abi_decoder_bytestring_cases >> disch_then (qspec_then `n` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >>
     simp[type_memory_bytes_def, abi_decode_bytes_copy_size_def, word_size_def] >>
     mp_tac (cj 3 abi_decoder_bytes_copy_size) >>
     simp[abi_decode_bytes_copy_size_def]) >>
  `n < dimword (:256) /\ cell+abi_decode_bytes_copy_size n < dimword (:256)` by
    (gvs[] >> decide_tac) >>
  `compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >> simp[]) >>
  `abi_decoder_metadata ce env ty tv (DecBytestring n) av v` by
    (qpat_x_assum `abi_decoder_metadata _ _ _ _ _ _ _` mp_tac >> simp[]) >>
  `entry_owned_region oid root extent cell (type_memory_bytes ce ty) s` by fs[] >>
  drule_all entry_canonical_bytes_owned_endpoint >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >> simp[array_child_result_def] >> gvs[]
QED

Theorem entry_conditional_base_producer:
  abi_decoder_coherent ce env ce.ce_struct_fields (BaseT bt) tv ==>
  entry_conditional_array_child_producer ce env (BaseT bt) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> Cases_on `bt`
  >~ [`BaseT (BytesT bound)`] >- (Cases_on `bound`
     >- (irule conditional_word_producer >> simp[Once type_to_abi_dec_info_def] >>
         goal_assum (drule_at Any)) >>
     irule conditional_bytes_producer >> simp[Once type_to_abi_dec_info_def] >>
     goal_assum (drule_at Any))
  >~ [`BaseT (StringT n)`] >- (irule conditional_bytes_producer >> simp[Once type_to_abi_dec_info_def] >>
     goal_assum (drule_at Any)) >>
  irule conditional_word_producer >> simp[Once type_to_abi_dec_info_def] >>
  goal_assum (drule_at Any)
QED

Theorem entry_conditional_flag_producer:
  abi_decoder_coherent ce env ce.ce_struct_fields (FlagT nsid) tv ==>
  entry_conditional_array_child_producer ce env (FlagT nsid) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> irule conditional_word_producer >>
  simp[Once type_to_abi_dec_info_def] >> goal_assum (drule_at Any)
QED

Theorem conditional_members_result[local]:
  canonical_members_effect ctx fn ambient cell sz st s t /\
  canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell sz last t /\
  val_in_memory tv v cell t.vs_memory /\
  abi_encoder_registered_effect ids [(cell,sz)] s t /\
  sz = type_memory_size tv ==>
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    st last cell tv v s t
Proof
  simp[canonical_members_effect_def, canonical_members_frame_def, array_child_result_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem entry_conditional_fixed_array_producer:
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  (!av v. entry_conditional_array_child_producer ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_conditional_array_child_producer ce env (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
    pav pv ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_conditional_array_child_producer_def] >>
  rpt gen_tac >> strip_tac >>
  `type_memory_size (ArrayTV tv (Fixed n)) = type_memory_bytes ce (ArrayT ty (Fixed n))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell (type_memory_bytes ce (ArrayT ty (Fixed n))) st s` by
    (simp[canonical_members_frame_def] >> gvs[]) >>
  `(!avs vs. pav = ListV avs /\
    pv = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\
    LENGTH vs = n /\ abi_decoder_members ce env ce.ce_struct_fields
      (REPLICATE n ty) (REPLICATE n tv) avs vs ==>
    !i. i < n ==> entry_conditional_array_child_producer ce env ty tv (EL i avs) (EL i vs)
      ctx fn oid root extent ambient b cap site limit_st)` by simp[] >>
  `cell + type_memory_bytes ce (ArrayT ty (Fixed n)) < dimword (:256)` by gvs[] >>
  drule_all entry_conditional_local_fixed_array_endpoint >> strip_tac >>
  qexists_tac `t` >> irule conditional_members_result >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem entry_conditional_dynamic_array_producer:
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) /\
  (!av v. entry_conditional_array_child_producer ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_conditional_array_child_producer ce env (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n))
    pav pv ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_conditional_array_child_producer_def] >>
  rpt gen_tac >> strip_tac >>
  `type_memory_size (ArrayTV tv (Dynamic n)) = type_memory_bytes ce (ArrayT ty (Dynamic n))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gvs[Excl "enc_def"] >>
  `entry_owned_region oid root extent cell (type_memory_bytes ce (ArrayT ty (Dynamic n))) s` by gvs[] >>
  `cell+type_memory_bytes ce (ArrayT ty (Dynamic n)) < dimword (:256)` by gvs[] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info ce.ce_struct_fields ce ty)`
  >- suspend "nonbulk"
  >> suspend "bulk"
QED
Resume entry_conditional_dynamic_array_producer[nonbulk]:
  `type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) n` by simp[Once type_to_abi_dec_info_def] >>
  irule entry_conditional_nonbulk_array_constructor >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` (irule_at Any) >>
  simp[Excl "enc_def", GSYM vyper_to_abi_type_def] >>
  goal_assum (drule_at Any) >> simp[Excl "enc_def"]
QED
Resume entry_conditional_dynamic_array_producer[bulk]:
  `~is_abi_dynamic ce.ce_struct_fields ty /\
   ~dec_info_needs_clamp (type_to_abi_dec_info ce.ce_struct_fields ce ty)` by fs[] >>
  `type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) F n` by
    simp[Once type_to_abi_dec_info_def] >>
  qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  `~dec_info_needs_clamp (type_to_abi_dec_info ce.ce_struct_fields ce ty)` by fs[] >>
  `mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic n))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (ArrayT ty (Dynamic n))) (ListV avs)` by
    simp[Excl "enc_def"] >>
  `sb+LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic n))) (ListV avs)) < dimword (:256)` by
    simp[Excl "enc_def"] >>
  drule_all entry_canonical_bulk_owned_endpoint >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  strip_tac >> qexists_tac `t` >> simp[array_child_result_def] >> gvs[Excl "enc_def"]
QED
Finalise entry_conditional_dynamic_array_producer
