(* Dynamic-array parent with fixed-function recursive children. *)
Theory abiMalformedOutcomeDynamic
Ancestors
  abiMalformedOutcomeParents abiMalformedOutcomeLoop abiMalformedInitTotal
  abiMalformedBoundedContract abiEncoder
  abiMalformedInitResource abiMalformedBulkCaller abiMalformedChildPremises
  abiMalformedZeroTraversal abiMalformedConstructorInduction
  abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderArrayInitReentry
  abiDecoderRecursiveArray exprSimAlloc rich_list abiDecoderDynarrayPrefix
  abiDecoderLoopCode abiDecoderCounters abiDecoderCode abiDecoderContract abiDecoderReentry
  abiMalformedOutcomeContract abiMalformedRecursiveInterface
  abiDecoderCoherence abiDecoderMemberInfos abiVyperAdmissible abiDecodeRanges
  exprLowering exprLoweringProps localPtrsProps emitHelperProps emitHelper context fragExec compileEnv
  vyperTypeSystem vyperTyping vyperValue vyperABI contractABI valueEncoding
  venomInst words list arithmetic

Theorem abi_malformed_bounded_dynamic_outcome:
  abi_decoder_coherent ce env sf ty tv /\
  abi_malformed_bounded_type_outcome ce env sf ty tv /\
  abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) ==>
  abi_malformed_bounded_type_outcome ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))` by
    simp[abi_decoder_coherent_array_iff] >>
  simp_tac bool_ss [abi_malformed_bounded_type_outcome_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_malformed_array_capacity >> simp[] >> strip_tac >>
  fs[Once type_to_abi_dec_info_def] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- suspend "recursive" >>
  `~is_abi_dynamic ce.ce_struct_fields ty /\ ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by fs[] >>
  fs[] >> irule abi_malformed_constructor_to_outcome >>
  irule abi_malformed_bulk_constructor_parent >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ce`, `sf`, `tv`] >> simp[Once type_to_abi_dec_info_def]
QED

Resume abi_malformed_bounded_dynamic_outcome[recursive]:
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  simp_tac bool_ss [abi_malformed_constructor_outcome_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_assum `abi_decoder_coherent ce env sf ty tv` (mp_tac o MATCH_MP abi_decoder_coherent_header) >> strip_tac >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)` by
    fs[abi_decoder_header_def] >>
  `32 <= outsz` by fs[type_memory_bytes_def] >>
  `maxn < dimword (:256)` by
    (qpat_assum `abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) _` mp_tac >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     drule (cj 1 evaluate_type_well_formed) >> simp[well_formed_type_value_def]) >>
  drule abi_decoder_recursive_array_code >> simp[] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  drule abi_malformed_init_shape >> strip_tac >>
  drule abi_decode_index_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `fn_has_code header_st allocation_st func` by
    (`cs_extends header_st loop_st` by
       (irule cs_extends_same_block >>
        metis_tac[inst_extends_def, IS_PREFIX_APPEND]) >>
     `cs_extends st header_st` by
       (drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
        drule_all abi_decode_array_header_shape >> strip_tac >>
        irule cs_extends_same_block >>
        metis_tac[inst_extends_trans, inst_extends_def, IS_PREFIX_APPEND]) >>
     `fn_has_code header_st loop_st func` by metis_tac[fn_has_code_split] >>
     `inst_extends header_st allocation_st` by
       metis_tac[abi_decode_alloc_buffer_inst_extends] >>
     `inst_extends allocation_st loop_st` by metis_tac[inst_extends_emit_void] >>
     `allocation_st.cs_blocks = header_st.cs_blocks /\
      allocation_st.cs_current_bb = header_st.cs_current_bb` by
       (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
        simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
     `cs_extends header_st allocation_st /\ cs_extends allocation_st loop_st` by
       (conj_tac >> irule cs_extends_same_block >>
        metis_tac[inst_extends_def, IS_PREFIX_APPEND]) >>
     metis_tac[fn_has_code_split]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `header_st.cs_next_id IN abi_malformed_scratch_sites st en func` by
    (simp[abi_malformed_scratch_sites_def] >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  drule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_malformed_init_fragment >> simp[] >>
  disch_then (qspecl_then [`abi_member_head_size (vyper_to_abi_type env ty)`,
    `(ip,cnt)`, `maxn`, `loop_st`, `ceiling`] mp_tac) >> simp[] >>
  strip_tac >> drule frag_outcome_apply >>
  disch_then (qspecl_then [`incoming`, `func`] mp_tac) >> simp[] >> strip_tac >>
  irule frag_outcome_compose >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >>
  `abi_malformed_entry ctx func cenv cx es loop_st
     (abi_malformed_scratch_sites st en func) dstid live
     base_op hi src dst B L xs p d outsz t` by
    (`local_ptrs_reserved cenv loop_st` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
        fs[abi_malformed_entry_def]) >>
     `EVERY (abi_decoder_operand_live loop_st.cs_next_var) [base_op;hi;src;dst]` by
       (fs[abi_malformed_entry_def, EVERY_DEF] >> rpt conj_tac >>
        irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     `abi_malformed_allocated_window live B L xs incoming /\
      live NOTIN abi_malformed_scratch_sites st en func /\ live <> dstid /\
      abi_malformed_destination func cenv es.scopes dstid d outsz incoming` by
       fs[abi_malformed_entry_def] >>
     drule_all abi_malformed_resource_window >> strip_tac >>
     drule_all abi_malformed_resource_destination >> strip_tac >>
     fs[abi_malformed_entry_def, abi_malformed_resource_post_def, EVERY_DEF]) >>
  FAIL_TAC "compiled loop"
QED

Finalise abi_malformed_bounded_dynamic_outcome
