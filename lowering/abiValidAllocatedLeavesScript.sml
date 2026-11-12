Theory abiValidAllocatedLeaves
Ancestors
  abiValidAllocatedContract abiValidDecodedMetadata abiDecoderValidBytesInput
  abiDecoderValidFixed abiValidBytes abiCanonicalHeadSize
  abiDecoderReentry abiDecoderBytes abiDecoderFrame
  compileEnv loweringStateRelDefs venomState valueEncoding valueEncodingProps finite_map words list arithmetic
  abiMalformedRecursiveInterface abiDecoderValidBytes abiDecoderContract
  abiDecoderBytesShape exprLoweringProps abiDecodeStaticProps venomMemDefs
  abiDecoderTypedContract abiDecoderBytesTyped
  abiValidAllocatedResource abiValidBytesReentry abiDecoderBytesFrame
  abiDecoderSequenceReach abiDecoderLoop emitHelperProps instIdxIndep venomInst
  abiDecoderTypedCompose abiMalformedSiteFrame
  abiDecoderPrimitiveMemory abiDecoderWordTyped abiDecoderCoherence abiDecoderReentryPointer abiDecoderClampedWord
  abiMalformedConstructorInduction abiValidStatic vyperABIValid contractABI

Theorem abi_valid_allocated_bytes_input:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?at payload.
    abi_decoder_valid_bytes_pre n at (DROP p xs) payload st src dst MLOAD
      base_op hi B p d (abi_decoder_prune_vars st.cs_next_var s) /\
    type_to_abi_dec_info sf ce ty = DecBytestring n /\
    type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
    (!mem. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem /\
      val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d mem ==>
      val_in_memory tv v d mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  drule_all abi_decoder_valid_bytes_metadata >>
  disch_then (qx_choose_then `at` (qx_choose_then `payload`
    (map_every assume_tac o CONJUNCTS))) >>
  mp_tac (INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``] abi_valid_bytes_lowering) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  `LENGTH xs = L` by metis_tac[LENGTH_mem_bytes_at] >>
  `vyper_decode_valid_enc at (DROP p xs)` by metis_tac[] >>
  drule_all abi_valid_bytes_decode >> strip_tac >>
  `p <= L` by fs[LENGTH_DROP] >>
  `mem_bytes_at (B+p) (LENGTH (DROP p xs)) s.vs_memory = DROP p xs` by
    (mp_tac (Q.SPECL [`B`, `p`, `LENGTH (DROP p (xs:word8 list))`, `L`, `s.vs_memory`]
      mem_bytes_at_window) >> simp[LENGTH_DROP] >>
     `TAKE (L-p) (DROP p xs) = DROP p xs` by
       (irule TAKE_LENGTH_TOO_LONG >> simp[LENGTH_DROP]) >> simp[]) >>
  `n < dimword (:256)` by
    (mp_tac (cj 3 abi_decoder_bytes_copy_size) >> strip_tac >>
     qpat_assum `d + type_memory_bytes ce ty < _` mp_tac >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `B+p+32+LENGTH payload <= d \/ d+abi_decode_bytes_copy_size n <= B+p` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     qhdtm_assum `abi_malformed_destination`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_destination_def]) >>
     qpat_x_assum `?cap. FLOOKUP s.vs_allocas live = _ /\ _` strip_assume_tac >>
     `B+cap <= b \/ b+sz <= B` by
       (fs[alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >>
     fs[LENGTH_DROP] >> decide_tac) >>
  qhdtm_assum `EVERY` (map_every assume_tac o CONJUNCTS o REWRITE_RULE [EVERY_DEF]) >>
  qexistsl_tac [`at`, `payload`] >>
  asm_simp_tac bool_ss [abi_decoder_valid_bytes_pre_def, abi_decoder_prune_fresh,
    abi_decoder_prune_eval, abi_decoder_prune_source, abi_decode_source_def,
    abi_decode_source_opcode_def] >>
  `B+p+LENGTH (DROP p xs) < dimword (:256)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `p+LENGTH (DROP p xs) <= L` by simp[LENGTH_DROP] >>
  (simp[] >> conj_tac >- gvs[] >>
   qexists_tac `L` >> simp[] >> decide_tac)
QED

Theorem abi_valid_allocated_bytes_reach:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?t. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_bytes_input >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),en)` by
    metis_tac[] >>
  drule_at (Pat `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_decoder_valid_bytes_reentry >>
  disch_then (qspecl_then [`en`, `ceiling`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ i.inst_opcode <> ALLOCA)
      (emitted_insts st en)` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac
     >- (qpat_x_assum `EVERY (\i. abi_decoder_reentry_opcode _) _` mp_tac >>
         simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
     qpat_x_assum `EVERY (\i. ~is_terminator _ /\ _) _` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> qexists_tac `i` >>
     simp[is_alloca_op_def]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s actual` by
    (irule abi_valid_allocated_scratch_free_resource >>
     metis_tac[]) >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule abi_decoder_inst_extends_prefix >> strip_tac >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `val_in_memory tv v d actual.vs_memory` by (first_x_assum irule >> simp[]) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
      d (type_memory_bytes ce ty) s actual` by
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

Theorem abi_valid_allocated_primitive_input:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  type_memory_bytes ce ty = 32 /\
  mem_bytes_at (B+p) 32 s.vs_memory =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) (DROP p xs)) /\
  B+p < dimword (:256) /\ d < dimword (:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule abi_malformed_constructor_primitive_metadata >>
  disch_then (qspecl_then [`DecPrimWord clamp`,
    `if is_dynamic (vyper_to_abi_type env ty) then 32 else static_length (vyper_to_abi_type env ty)`] mp_tac) >>
  (impl_tac >- simp[]) >>
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [])) >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  `~is_dynamic (vyper_to_abi_type env ty) /\ static_length (vyper_to_abi_type env ty) = 32` by
    (metis_tac[]) >>
  `p+32 <= L` by metis_tac[] >>
  `LENGTH xs = L` by metis_tac[LENGTH_mem_bytes_at] >>
  `valid_enc (vyper_to_abi_type env ty) (DROP p xs)` by
    (irule vyper_decode_valid_enc_static >> simp[]) >>
  drule abi_static_prefix_static >>
  simp_tac bool_ss [abi_static_prefix_def] >>
  disch_then (qspec_then `DROP p xs` mp_tac) >>
  (impl_tac >- simp[LENGTH_DROP]) >> strip_tac >>
  `mem_bytes_at (B+p) 32 s.vs_memory = TAKE 32 (DROP p xs)` by
    (gvs[mem_bytes_at_window]) >>
  simp[] >> decide_tac
QED

Theorem abi_valid_allocated_primitive_reach:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?t. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_primitive_input >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),en)` by
    metis_tac[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `mem_bytes_at (B+p) 32 (abi_decode_source MLOAD s) =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) (DROP p xs))` by
    simp[abi_decode_source_def] >>
  qhdtm_assum `EVERY` (map_every assume_tac o CONJUNCTS o REWRITE_RULE [EVERY_DEF]) >>
  drule_all abi_decoder_primitive_memory_reentry >> strip_tac >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
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
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
      d (type_memory_bytes ce ty) s actual` by
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
