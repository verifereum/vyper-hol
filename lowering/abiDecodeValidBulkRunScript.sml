Theory abiDecodeValidBulkRun
Ancestors
  abiValidAllocatedBulk abiValidAllocatedResource abiValidAllocatedContract
  abiDecoderBulkExecute abiDecoderSequenceReach abiDecoderContract
  abiMalformedRecursiveInterface abiDecoderReentry exprLoweringProps
  instIdxIndep venomInst venomState list
  abiMalformedSiteFrame compileEnv loweringStateRelDefs abiDecoderBulk
  abiDecoderTypedCompose abiValidDecodedMetadata abiStaticLayoutProps
  abiDecoderTypedContract abiDecoderLayout vyperABI vyperTyping venomMemDefs
  valueEncodingDefs

Theorem abi_valid_allocated_bulk_reach_run:
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  abi_valid_allocated_entry H ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?actual. run_inst_seq (emitted_insts st en) s = OK actual /\
    abi_valid_allocated_post (ArrayTV tv (Dynamic maxn)) v
      ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s
      (actual with vs_inst_idx := LENGTH en.cs_current_insts) /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_bulk_sequence >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi
      (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en)` by metis_tac[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by
    (qpat_assum `EVERY (\i. _ /\ _ /\ _) _` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ i.inst_opcode <> ALLOCA)
      (emitted_insts st en)` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac
     >- (qpat_x_assum `EVERY (\i. abi_decoder_reentry_opcode _) _` mp_tac >>
         simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
     qpat_x_assum `EVERY (\i. _ /\ _ /\ _) _` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> qexists_tac `i` >>
     simp[is_alloca_op_def]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s actual` by
    (irule abi_valid_allocated_scratch_free_resource >> metis_tac[]) >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  `inst_extends st en` by (irule abi_decoder_inst_extends_prefix >> simp[]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `reached` strip_assume_tac)) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s actual` by
    (irule abi_valid_allocated_frame_scratch_free >> simp[]) >>
  qexists_tac `actual` >>
  qpat_x_assum `reached = _` SUBST_ALL_TAC >>
  qhdtm_assum `abi_malformed_resource_post`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
  qhdtm_assum `abi_valid_allocated_frame`
    (assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_frame_def, abi_malformed_site_range_def]) >>
  simp[abi_valid_allocated_post_def, fresh_vars_wrt_def,
    abi_malformed_resource_post_def, stmt_state_rel_inst_idx, eval_op_inst_idx,
    abi_valid_allocated_frame_def, abi_malformed_site_range_def] >>
  qhdtm_x_assum `abi_valid_allocated_entry` kall_tac >>
  conj_tac >- fs[fresh_vars_wrt_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_valid_allocated_bulk_count:
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  abi_valid_allocated_entry H ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?vs. v = ArrayV (DynArrayV vs) /\ all_have_type tv vs /\
    LENGTH vs <= maxn /\ mload (B+p) s = n2w (LENGTH vs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule_all abi_valid_decoded_metadata >>
  simp_tac bool_ss [abi_decoder_metadata_def] >> strip_tac >>
  `DecDynArray ei abi_sz mem_sz F maxn = type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[static_layout_compatible_properties] >>
  drule_all abi_valid_allocated_bulk_window >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_decoder_typed_conversion >> strip_tac >>
  `?vs. v = ArrayV (DynArrayV vs) /\ all_have_type tv vs /\ LENGTH vs <= maxn` by
    (Cases_on `v` >> fs[Once value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV a)` >> Cases_on `a` >> fs[Once value_has_type_def]) >>
  pop_assum strip_assume_tac >>
  `?avs. vyper_to_abi_same env ty vs = SOME avs /\
    dec (Array NONE (vyper_to_abi_type env ty)) (DROP p xs) = ListV avs` by
    (qpat_x_assum `vyper_to_abi env (ArrayT _ _) _ = _` mp_tac >>
     asm_simp_tac bool_ss [Once vyper_to_abi_def, vyper_to_abi_type_def] >>
     simp_tac bool_ss [AllCaseEqs(), optionTheory.NOT_NONE_SOME, optionTheory.SOME_11] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `mem_bytes_at (B+p) (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) s.vs_memory =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by metis_tac[] >>
  drule_all static_dynarray_source_windows >> strip_tac >>
  qexists_tac `vs` >> fs[mload_def, mem_word_at_def, mem_bytes_at_def]
QED
