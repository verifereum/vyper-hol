Theory exprSimAbiDecodeOwnedMember
Ancestors
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeScratchCover
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeSiteProvenance
  abiDecoderDynamicLoopSetup abiDecoderMemberCode
  abiDecoderMemberSetup abiDecoderCounters abiDecoderContract
  abiDecoderSiteEffect abiValidMember abiValidAggregateHeads
  abiDecoderBytestringOutcome abiDecodeRanges
  emitHelperProps exprLoweringProps venomState
  abiDecoderAppend abiDecoderSequenceReach abiValidMembers
  vyperABI contractABI fragExec compileEnv
  finite_map pred_set words list arithmetic

Theorem abi_decode_owned_address_frame:
  abi_decode_owned sites scratch d n s /\
  abi_decoder_address_frame next s t ==>
  abi_decode_owned sites scratch d n t
Proof
  simp[abi_decode_owned_def, abi_decode_scratch_cover_def,
       abi_decoder_address_frame_def] >> metis_tac[]
QED

Theorem abi_decode_owned_member_conditional_outcome:
  abi_decode_owned_child_contract ce env ty tv /\
  abi_decode_member_setup dst src MLOAD base_op hi
    (is_dynamic (vyper_to_abi_type env ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),last) /\
  abi_decode_code_context func fn st last /\
  last.cs_next_var <= limit_st.cs_next_var /\
  abi_decode_sites st.cs_next_id last.cs_next_id SUBSET sites /\
  abi_decode_owned sites scratch (d+vo) (type_memory_bytes ce ty) s /\
  abi_decode_member_pre ctx func ce env ty tv limit_st next
    (scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce ty}) sites
    st dst src base_op hi B bs p d ao vo delta s ==>
  abi_decode_context_result ctx func fn tv limit_st next
    (scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce ty})
    (abi_decode_sites st.cs_next_id last.cs_next_id) last
    (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p bs)
      (DROP ao (DROP p bs))) env ty (d+vo) s
Proof
  strip_tac >>
  drule exprSimAbiDecodeMemberOutcomeTheory.abi_decode_member_mload_setup_shape >> strip_tac >>
  `cs_extends st middle` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends middle last` by (irule cs_extends_abi_decode >> metis_tac[]) >>
  `fn_has_code st middle fn /\ fn_has_code middle last fn` by
    (irule fn_has_code_split >> fs[abi_decode_code_context_def]) >>
  `middle.cs_next_var <= limit_st.cs_next_var` by
    (drule abi_decoder_variable_counter >> decide_tac) >>
  `abi_decode_code_context func fn middle last` by
    (irule abi_decode_code_context_after_setup >> metis_tac[]) >>
  `abi_decode_sites middle.cs_next_id last.cs_next_id SUBSET
     abi_decode_sites st.cs_next_id last.cs_next_id` by
    (`st.cs_next_id < middle.cs_next_id` by
       (drule abiDecoderMemberCodeTheory.abi_decode_member_setup_shape >>
        simp[abi_decode_source_opcode_def]) >>
     simp[abi_decode_sites_def, SUBSET_DEF] >> decide_tac) >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
    abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta` by
    (strip_tac >> qhdtm_assum `abi_decode_member_pre`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_member_pre_def]) >>
     pure_rewrite_tac[ADD_ASSOC] >> qpat_x_assum `delta = _` SUBST1_TAC >>
     irule abi_decode_member_offset_load >> metis_tac[]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty) /\ dimword(:256) <= p+delta`
  >- (qhdtm_assum `abi_decode_member_pre`
        (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_member_pre_def]) >>
      `delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s)` by
        (fs[GSYM ADD_ASSOC] >>
         simp[abi_head_word_def, dec_number_def, dest_NumV_def, w2n_lt]) >>
      `?u. Dabort ctx fn s Revert_abort u` by
        (fs[abi_decode_entry_def] >>
         drule abi_decode_member_setup_wrap_abort_reentry >>
         disch_then irule >>
         simp[EVERY_DEF] >> conj_tac
         >- (qexistsl_tac [`B`, `LENGTH bs`, `p`] >>
             simp[AC ADD_ASSOC ADD_COMM]) >>
         qexists_tac `limit_st` >> simp[]) >>
      `~vyper_decode_valid_enc (vyper_to_abi_type env ty)
        (abi_decode_member_bytes (vyper_to_abi_type env ty)
          (DROP p bs) (DROP ao (DROP p bs)))` by
        (irule abi_decode_member_wrap_source_reject >>
         simp[] >> qexists_tac `LENGTH bs` >> simp[] >> decide_tac) >>
      simp[abi_decode_context_result_def, abi_decode_source_accepts_def] >>
      metis_tac[]) >>
  qhdtm_assum `abi_decode_member_pre`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_member_pre_def]) >>
  `p+(if is_dynamic (vyper_to_abi_type env ty) then delta else ao) < dimword(:256)` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >> fs[] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var base_op` by fs[] >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
     eval_operand base_op s = SOME(n2w B) /\
     abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta /\
     p+delta < dimword(:256)` by (strip_tac >> fs[] >> decide_tac) >>
  qhdtm_assum `abi_decode_entry` (strip_assume_tac o REWRITE_RULE [abi_decode_entry_def]) >>
  drule_all exprSimAbiDecodeMemberExecuteTheory.abi_decode_member_mload_setup_reach >>
  disch_then (qspecl_then
    [`scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce ty}`,
     `abi_decode_sites st.cs_next_id last.cs_next_id`] strip_assume_tac) >>
  `abi_decode_entry middle t` by simp[abi_decode_entry_def] >>
  drule_all abi_decode_member_child_pre >> strip_tac >>
  `abi_decode_sites middle.cs_next_id last.cs_next_id SUBSET sites` by
    metis_tac[SUBSET_TRANS] >>
  `abi_decode_owned sites scratch (d+vo) (type_memory_bytes ce ty) t` by
    metis_tac[abi_decode_owned_address_frame] >>
  qhdtm_x_assum `abi_decode_owned_child_contract`
    (assume_tac o PURE_REWRITE_RULE [abi_decode_owned_child_contract_def]) >>
  first_x_assum drule_all >> strip_tac >>
  `decode_site_effect ctx func next
    (scratch UNION {a | d+vo <= a /\ a < d+vo+type_memory_bytes ce ty}) s t` by
    (irule decode_site_effect_threshold >> metis_tac[]) >>
  `abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p bs)
      (DROP ao (DROP p bs)) =
    abi_decode_source_view (vyper_to_abi_type env ty) bs
      (p+if is_dynamic (vyper_to_abi_type env ty) then delta else ao)` by
    (irule abi_decode_member_contextual_view >> simp[]) >>
  qpat_x_assum `abi_decode_member_bytes _ _ _ = _` SUBST1_TAC >>
  drule_all abi_decode_context_result_prefix >> simp[]
QED
