Theory abiValidAllocatedBulkReach
Ancestors
  abiValidAllocatedBulk abiValidAllocatedResource abiValidAllocatedContract
  abiDecoderBulkExecute abiDecoderSequenceReach abiDecoderContract
  abiMalformedRecursiveInterface abiDecoderReentry exprLoweringProps
  emitHelperProps instIdxIndep venomInst venomState list
  abiMalformedSiteFrame compileEnv abiDecoderBulk abiDecoderTypedCompose

Theorem abi_valid_allocated_bulk_reach:
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  abi_valid_allocated_entry ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?t. abi_valid_allocated_post (ArrayTV tv (Dynamic maxn)) v
      ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_bulk_sequence >> strip_tac >>
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
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s actual` by
    (irule abi_valid_allocated_frame_scratch_free >> simp[]) >>
  qexists_tac `t` >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qhdtm_assum `abi_malformed_resource_post`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
  qhdtm_assum `abi_valid_allocated_frame`
    (assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_frame_def, abi_malformed_site_range_def]) >>
  simp[abi_valid_allocated_post_def, fresh_vars_wrt_def,
    abi_malformed_resource_post_def, stmt_state_rel_inst_idx, eval_op_inst_idx,
    abi_valid_allocated_frame_def, abi_malformed_site_range_def] >>
  qpat_x_assum `abi_valid_allocated_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  conj_tac >- fs[fresh_vars_wrt_def] >> first_assum ACCEPT_TAC
QED
