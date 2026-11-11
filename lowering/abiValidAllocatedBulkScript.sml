Theory abiValidAllocatedBulk
Ancestors
  abiValidAllocatedContract abiValidAllocatedLeaves abiValidDecodedMetadata
  abiValidStatic abiCanonicalHeadSize vyperABIValid abiDecoderLayout
  abiDecoderBulk abiDecoderBulkExecute abiDecoderBulkReentry
  abiMalformedRecursiveInterface abiDecoderContract venomMemDefs
  valueEncoding valueEncodingProps compileEnv contractABI words list arithmetic vyperABI
  abiDecoderTypedContract abiDecoderCoherence abiDecoderReentry abiDecoderVarSequence
  abiDecoderVarExtend abiDecoderReentryPointer abiDecoderGuard abiStaticDynarrayLayout
  abiStaticLayoutProps finite_map vyperValue vyperTyping venomState byte exprLoweringProps
  abiDecoderFrameCompose emitHelperProps

Theorem abi_valid_allocated_static_window:
  ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  mem_bytes_at (B+p) (static_length (vyper_to_abi_type env ty)) s.vs_memory =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) (DROP p xs))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  `p + static_length (vyper_to_abi_type env ty) <= L` by metis_tac[] >>
  `LENGTH xs = L` by metis_tac[LENGTH_mem_bytes_at] >>
  `valid_enc (vyper_to_abi_type env ty) (DROP p xs)` by
    (irule vyper_decode_valid_enc_static >> simp[]) >>
  drule abi_static_prefix_static >>
  simp_tac bool_ss [abi_static_prefix_def] >>
  disch_then (qspec_then `DROP p xs` mp_tac) >>
  (impl_tac >- simp[LENGTH_DROP]) >> strip_tac >>
  gvs[mem_bytes_at_window]
QED

Theorem abi_valid_bulk_array_strict[local]:
  ~is_dynamic at /\ vyper_decode_valid_enc (Array NONE at) bs ==>
  valid_enc (Array NONE at) bs
Proof
  strip_tac >>
  qpat_x_assum `vyper_decode_valid_enc (Array NONE at) bs` mp_tac >>
  simp_tac bool_ss [Once vyper_decode_valid_enc_def, Once valid_enc_def, LET_THM] >>
  strip_tac >> gvs[] >>
  irule (cj 2 vyper_decode_valid_enc_static_mutual) >> simp[]
QED

Theorem abi_valid_allocated_bulk_window:
  ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_valid_allocated_entry ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  let at = Array NONE (vyper_to_abi_type env ty) in
  let av = dec at (DROP p xs) in
  LENGTH (enc at av) <= L-p /\
  mem_bytes_at (B+p) (LENGTH (enc at av)) s.vs_memory = enc at av
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  `LENGTH xs = L` by metis_tac[LENGTH_mem_bytes_at] >>
  `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)` by
    (qpat_assum `vyper_decode_valid_enc (vyper_to_abi_type _ _) _`
       (mp_tac o PURE_REWRITE_RULE [vyper_to_abi_type_def]) >> simp_tac bool_ss []) >>
  drule_all abi_valid_bulk_array_strict >> strip_tac >>
  drule_all abi_valid_static_array_prefix >> strip_tac >>
  `p <= L` by
    (qpat_x_assum `vyper_decode_valid_enc (Array NONE _) _` mp_tac >>
     simp[Once vyper_decode_valid_enc_def, LENGTH_DROP, LET_THM] >> decide_tac) >>
  conj_tac >- (qpat_assum `LENGTH (enc _ _) <= _` mp_tac >> simp_tac bool_ss [LENGTH_DROP] >> metis_tac[]) >>
  `mem_bytes_at (B+p) (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
      (dec (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)))) s.vs_memory =
    TAKE (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
      (dec (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)))) (DROP p xs)` by
    (mp_tac (Q.SPECL [`B`, `p`, `LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
       (dec (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)))`, `L`, `s.vs_memory`]
       mem_bytes_at_window) >> simp_tac bool_ss [] >>
     impl_tac >- (qpat_assum `LENGTH (enc _ _) <= _` mp_tac >>
       simp_tac bool_ss [LENGTH_DROP] >> simp[] >> decide_tac) >>
     gvs[]) >>
  metis_tac[]
QED

Theorem abi_valid_allocated_bulk_sequence:
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  abi_valid_allocated_entry ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?actual. run_inst_seq (emitted_insts st en) s = OK actual /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) v d actual.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s actual /\
    fresh_vars_wrt ceiling actual /\ actual.vs_allocas = s.vs_allocas /\
    actual.vs_alloca_next = s.vs_alloca_next /\ actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
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
  drule_all static_same_canonical_layout >> strip_tac >>
  `LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) =
    32 + LENGTH vs * type_memory_size tv` by
    simp[static_dynarray_encoding, LENGTH_word_to_bytes, Excl "enc_def"] >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  `LENGTH xs = L` by metis_tac[LENGTH_mem_bytes_at] >>
  `p <= L` by
    (qpat_x_assum `vyper_decode_valid_enc _ _` mp_tac >>
     simp[vyper_to_abi_type_def, Once vyper_decode_valid_enc_def, LENGTH_DROP, LET_THM] >> decide_tac) >>
  `p+32+LENGTH vs * mem_sz <= L /\
   B+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
   LENGTH vs * mem_sz < dimword (:256)` by
    (qpat_x_assum `LENGTH (enc _ _) <= _` mp_tac >>
     asm_simp_tac bool_ss [] >>
     `LENGTH vs * mem_sz <= maxn * mem_sz` by simp[LE_MULT_RCANCEL] >> decide_tac) >>
  `B+p+32+LENGTH vs * mem_sz <= d \/ d+32 <= B+p+32` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     qhdtm_assum `abi_malformed_destination`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_destination_def]) >>
     qpat_x_assum `?cap. FLOOKUP s.vs_allocas live = _ /\ _` strip_assume_tac >>
     `B+cap <= b \/ b+sz <= B` by
       (fs[alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >>
     decide_tac) >>
  `mem_bytes_at (B+p) (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) s.vs_memory =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by metis_tac[] >>
  drule_all static_dynarray_source_windows >> strip_tac >>
  `abi_decode_load MLOAD (n2w (B+p) : bytes32) s = n2w (LENGTH vs)` by
    (simp[abi_decode_load_def, mload_def, w2n_n2w] >>
     qpat_x_assum `mem_word_at (B+p) _ = _` mp_tac >>
     simp[mem_word_at_def, mem_bytes_at_def]) >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en)` by metis_tac[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `L < dimword (:256)` by decide_tac >>
  qhdtm_assum `EVERY` (map_every assume_tac o CONJUNCTS o REWRITE_RULE [EVERY_DEF]) >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var s`,
    `sb` |-> `p`, `src_base` |-> `B`, `n` |-> `LENGTH (vs:vyperValue$value list)`,
    `st'` |-> `en`, `opc` |-> `MLOAD`] abi_decode_bulk_sequence) >>
  (impl_tac >- (asm_simp_tac bool_ss [abi_decoder_prune_fresh, abi_decoder_prune_eval] >>
    simp_tac bool_ss [abi_decoder_prune_vars_def, abi_decode_load_def, mload_def] >>
    simp[w2n_n2w, LET_THM] >>
    conj_tac >- (qpat_x_assum `mem_word_at (B+p) _ = _` mp_tac >>
        simp[mem_word_at_def, mem_bytes_at_def]) >>
    qexists_tac `L` >> asm_simp_tac bool_ss [] >>
    conj_tac >- (irule EQ_SYM >> irule LESS_MOD >> simp[]) >>
    qpat_assum `p+32+LENGTH vs * mem_sz <= L` mp_tac >>
    qpat_assum `mem_sz = type_memory_size tv` (fn th => pure_rewrite_tac [GSYM th]) >>
    POP_ASSUM_LIST (K all_tac) >> decide_tac)) >> strip_tac >>
  rename1 `run_inst_seq _ (abi_decoder_prune_vars st.cs_next_var s) = OK clean` >>
  `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d clean.vs_memory` by
    (qpat_assum `mem_bytes_at (d+32) _ clean.vs_memory = _`
       (assume_tac o SRULE [abi_decoder_prune_vars_def, abi_decode_source_def]) >>
     irule static_dynarray_copied_layout >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`avs`, `ce`, `env`, `B+p`, `s.vs_memory`, `ty`] >>
     asm_simp_tac bool_ss [] >>
     qpat_assum `mem_bytes_at (d+32) _ clean.vs_memory = _` mp_tac >>
     qpat_assum `mem_sz = type_memory_size tv` (fn th => pure_rewrite_tac [th]) >>
     simp_tac bool_ss [abi_decoder_prune_vars_def, abi_decode_source_def] >>
     disch_then SUBST1_TAC >> asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend s.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `abi_decode_frame d (32 + LENGTH vs * mem_sz) s actual` by
    (drule_all abi_decoder_reentry_frame >> simp[]) >>
  `abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`d`, `32+LENGTH vs * mem_sz`] >>
     simp[LE_MULT_RCANCEL]) >>
  `fresh_vars_wrt ceiling clean` by
    (irule fresh_vars_wrt_mono >> qexists_tac `en` >> simp[GREATER_EQ]) >>
  `fresh_vars_wrt ceiling actual` by
    (irule abi_decoder_vars_extend_fresh >> qexistsl_tac [`s.vs_vars`, `clean`] >>
     fs[fresh_vars_wrt_def, GREATER_EQ]) >>
  drule_all abiDecoderArrayInitExecTheory.abi_decoder_guard_sequence_fields >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_decoder_prune_vars_def] >>
  rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars st.cs_next_var s) = SOME w` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `eval_operand op clean = SOME w` by metis_tac[] >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED
