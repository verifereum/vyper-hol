(* Reentrant bulk execution, with copy ownership used only after guards pass. *)
Theory exprSimAbiDecodeBulkOwned
Ancestors
  loweringStateRelDefs valueEncodingDefs
  exprSimAbiDecodeArrayFetched exprSimAbiDecodeArrayPrepareReentry
  exprSimAbiDecodePrimitiveOwned exprSimAbiDecodeArrayClosure exprSimAbiDecodeMemberExecute
  abiDecoderReentry abiDecoderReentryPointer abiDecoderVarExtend
  abiDecoderBulkExecute abiDecoderBulk abiDecoderSiteEffect
  abiDecoderContract abiDecoderWordOutcome abiDecoderBytestringOutcome abiDecoderVarSequence
  abiDecoderLayout abiStaticLayoutProps abiCanonicalHeadSize
  abiDecoderCoherence exprSimAbiDecodeOwnedContext vyperABI contractABI
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound emitHelper emitHelperProps compileEnv abiDecodeRanges
  venomExecSemantics venomState venomInst valueEncoding arithmetic list rich_list
  abiDecoderSequenceReach abiDecoderFiniteControl exprLoweringProps fragExec
  exprLowering vyperValue vyperAST vyperTypeSystem exprSimAbiDecodeWidthBoundary
  valueEncodingProps valueEncodingProofs abiDecoderFrame pred_set
  exprSimAbiDecodeSiteProvenance

Theorem abi_decode_array_bulk_success_reentry:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  eval_operand src s = SOME(n2w pos) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w b) /\
  abi_decode_load MLOAD (n2w (b+pos):bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword(:256) /\
  b+pos+32 < dimword(:256) /\ d+32 < dimword(:256) /\
  n*mem_sz < dimword(:256) /\
  (b+pos+32+n*mem_sz <= d \/ d+32 <= b+pos+32) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME(n2w h) /\
    pos+32+n*abi_sz <= h /\ h < dimword(:256)) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  next <= st.cs_next_var /\ decode_site_resources ctx func s /\
  {a | d <= a /\ a < d+32+n*mem_sz} SUBSET writes ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d+32) (n*mem_sz) t.vs_memory =
      mem_bytes_at (b+pos+32) (n*mem_sz) s.vs_memory /\
    fresh_vars_wrt limit_st t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    decode_site_effect ctx func next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `decode_site_resources ctx func (abi_decoder_prune_vars st.cs_next_var s)` by
    (irule decode_site_resources_fields >> qexists `s` >>
     simp[abi_decoder_prune_vars_def]) >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w pos) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w d) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w b)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `abi_decode_load MLOAD (n2w (b+pos):bytes32)
    (abi_decoder_prune_vars st.cs_next_var s) = n2w n` by
    fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def] >>
  `hi = Lit 0w \/ ?h. eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w h) /\
    pos+32+n*abi_sz <= h /\ h < dimword(:256)` by
    (asm_simp_tac bool_ss [abi_decoder_prune_eval] >> simp[] >> metis_tac[]) >>
  drule_all abi_decode_array_bulk_memory_opcodes >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    (fs[EVERY_MEM, abi_bytes_opcode_def, abi_word_opcode_def,
        abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  drule abi_decode_array_bulk_success_effect >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand base_op _ = _`)) >>
  disch_then (drule_at (Pat `abi_decode_load _ _ _ = _`)) >>
  disch_then (drule_at (Pat `decode_site_resources _ _ _`)) >>
  disch_then (qspecl_then [`writes`,`next`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[])) >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `decode_site_effect ctx func next writes s actual` by
    (drule_all abi_decode_primitive_reentry_effect >> simp[]) >>
  qexists `actual` >> gvs[abi_decoder_prune_vars_def]
QED

Theorem abi_decode_array_bulk_source_reentry:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_member_head_size (vyper_to_abi_type env ty))
      (type_memory_bytes ce ty) F maxn) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w pos) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w b) /\ eval_operand hi s = SOME(n2w h) /\
  n = w2n (mem_word_at (b+pos) s.vs_memory) /\
  bs = mem_bytes_at (b+pos) (h-pos) s.vs_memory /\
  pos < dimword(:256) /\ h < dimword(:256) /\ b+h < dimword(:256) /\
  maxn < dimword(:256) /\ type_memory_bytes ce ty < dimword(:256) /\
  (n <= maxn ==> n*abi_member_head_size (vyper_to_abi_type env ty) < dimword(:256)) /\
  d+32 < dimword(:256) /\ (b+h <= d \/ d+32 <= b+pos+32) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  next <= st.cs_next_var /\ decode_site_resources ctx func s /\
  (n <= maxn ==> {a | d <= a /\ a < d+32+n*type_memory_bytes ce ty} SUBSET writes) ==>
  (?t v. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) bs v /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) v d t.vs_memory /\
    fresh_vars_wrt limit_st t /\
    decode_site_effect ctx func next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    ~(?v. abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) bs v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_member_head_size (vyper_to_abi_type env ty) = type_memory_bytes ce ty` by
    (`static_layout_compatible ce env ty tv` by
       metis_tac[abi_decoder_unclamped_static_layout] >>
     drule static_layout_compatible_properties >> simp[abi_member_head_size_def]) >>
  Cases_on `n <= maxn /\ pos+32+n*abi_member_head_size (vyper_to_abi_type env ty) <= h`
  >- suspend "success"
  >> suspend "reject"
QED
Resume abi_decode_array_bulk_source_reentry[success]:
  qpat_x_assum `n <= maxn /\ _` strip_assume_tac >>
  `b+pos+32 < dimword(:256) /\ n*type_memory_bytes ce ty < dimword(:256) /\
   (b+pos+32+n*type_memory_bytes ce ty <= d \/ d+32 <= b+pos+32)` by
    (gvs[] >> decide_tac) >>
  `abi_decode_load MLOAD (n2w (b+pos):bytes32) s = n2w n` by
    simp[abi_decode_load_def, abi_decode_source_def, mload_def, mem_word_at_def, mem_bytes_at_def] >>
  drule abi_decode_array_bulk_success_reentry >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand base_op _ = _`)) >>
  disch_then (drule_at (Pat `abi_decode_load _ _ _ = _`)) >>
  disch_then (drule_at (Pat `decode_site_resources _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspecl_then [`writes`,`next`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> qexists `h` >> gvs[])) >> strip_tac >>
  `pos+32+n*type_memory_bytes ce ty <= h` by metis_tac[] >>
  drule_all abi_decode_array_bulk_suffix_memory >> strip_tac >>
  disj1_tac >> qexistsl [`t`,`v`] >>
  gvs[abi_decode_source_accepts_def, vyper_to_abi_type_def]
QED
Resume abi_decode_array_bulk_source_reentry[reject]:
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  qpat_x_assum `abi_member_head_size _ = _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  drule_all abi_decode_dynarray_memory_prefix_reject_reentry >>
  disch_then (qspecl_then [`ty`,`env`] strip_assume_tac) >>
  `abi_decode_bulk_body dst src addr MLOAD base_op
    (type_memory_bytes ce ty) cs' = ((),st')` by
    (qpat_x_assum `(\(addr,cs'). _) _ = _` mp_tac >> simp[]) >>
  drule_all abi_decode_bulk_body_shape >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all run_inst_seq_abort_extends >> strip_tac >>
  disj2_tac >> qexists `t` >>
  gvs[abi_decode_source_accepts_def, vyper_to_abi_type_def]
QED
Finalise abi_decode_array_bulk_source_reentry

Theorem abi_decode_array_bulk_fetched_reentry:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_member_head_size (vyper_to_abi_type env ty))
      (type_memory_bytes ce ty) F maxn) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w pos) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w b) /\ eval_operand hi s = SOME(n2w h) /\
  n = w2n (mem_word_at (b+pos) s.vs_memory) /\
  bs = mem_bytes_at (b+pos) (h-pos) s.vs_memory /\
  pos < dimword(:256) /\ h < dimword(:256) /\ b+h < dimword(:256) /\
  maxn < dimword(:256) /\ type_memory_bytes ce ty < dimword(:256) /\
  (n <= maxn ==> n*abi_member_head_size (vyper_to_abi_type env ty) < dimword(:256)) /\
  d+32 < dimword(:256) /\ (b+h <= d \/ d+32 <= b+pos+32) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  next <= st.cs_next_var /\ decode_site_resources ctx func s /\
  (n <= maxn ==> {a | d <= a /\ a < d+32+n*type_memory_bytes ce ty} SUBSET writes) /\
  fn_has_code st st' fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?t v. Dreach ctx fn s t /\
    abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) bs v /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) v d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ decode_site_effect ctx func next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_entry st' t) \/
  (?u. Dabort ctx fn s Revert_abort u /\
    ~(?v. abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) bs v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  `inst_extends st st'` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  drule_all abi_decode_array_bulk_source_reentry >> strip_tac
  >- (drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      disj1_tac >> qexistsl_tac [`t'`, `v`] >>
      conj_tac >- metis_tac[Dreach_straight_prefix] >>
      gvs[abi_decode_entry_def, fresh_vars_wrt_def, decode_site_effect_inst_idx] >>
      fs[decode_site_effect_def, decode_static_frame_def, venom_state_component_equality]) >>
  drule_all abi_decoder_run_sequence_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  disj2_tac >> simp_tac bool_ss [Dabort_def] >>
  qexists `t with vs_inst_idx := n'` >> conj_tac
  >- (qexists `0` >> asm_rewrite_tac[]) >> gvs[]
QED

Theorem abi_decode_array_bulk_owned_contract:
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info ce.ce_struct_fields ce ty) ==>
  abi_decode_owned_child_contract ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >> simp_tac bool_ss [abi_decode_owned_child_contract_def] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_decode_context_pre` mp_tac >>
  simp_tac bool_ss [abi_decode_context_pre_def] >> strip_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` by
    fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `assignable_type env ty /\ abi_decode_bytes_widths env ty` by
    fs[assignable_type_def, abi_decode_bytes_widths_def] >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (abi_member_head_size (vyper_to_abi_type env ty))
      (type_memory_bytes ce ty) F maxn) st = ((),last)` by
    gvs[type_to_abi_dec_info_def] >>
  `maxn < dimword(:256)` by
    (qpat_x_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` mp_tac >>
     simp_tac bool_ss [abi_decoder_coherent_array_iff, abi_decoder_header_def] >>
     strip_tac >> fs[Once evaluate_type_def, type_slot_size_def, AllCaseEqs()] >>
     `maxn <= maxn * type_slot_size tv` by
       (simp[LE_MULT_CANCEL_LBARE] >> decide_tac) >> decide_tac) >>
  `abi_embedded_static_size ce.ce_struct_fields ty <= type_memory_bytes ce ty` by
    metis_tac[abi_decode_embedded_head_le_memory] >>
  `!n. n <= maxn ==> n*abi_member_head_size (vyper_to_abi_type env ty) < dimword(:256)` by
    (rpt strip_tac >>
     `n*abi_member_head_size (vyper_to_abi_type env ty) <= maxn*type_memory_bytes ce ty` by
       (irule LESS_MONO_MULT2 >> metis_tac[]) >>
     fs[type_memory_bytes_def] >> decide_tac) >>
  `d+32 < dimword(:256) /\ LENGTH bs < dimword(:256)` by
    (fs[type_memory_bytes_def] >> decide_tac) >>
  `0 < maxn` by
    (qpat_x_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` mp_tac >>
     simp_tac bool_ss [abi_decoder_coherent_array_iff, abi_decoder_header_def] >>
     strip_tac >> fs[Once evaluate_type_def, bound_length_def, AllCaseEqs()]) >>
  `type_memory_bytes ce ty < dimword(:256)` by
    (`type_memory_bytes ce ty <= maxn*type_memory_bytes ce ty` by
       (simp[LE_MULT_CANCEL_LBARE] >> decide_tac) >>
     qpat_x_assum `d + type_memory_bytes ce (ArrayT _ _) < _` mp_tac >>
     simp_tac bool_ss [type_memory_bytes_def] >> decide_tac) >>
  `abi_decode_source_view (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) bs pos =
    mem_bytes_at (B+pos) (LENGTH bs-pos) s.vs_memory` by
    (simp[abi_decode_source_view_def, vyper_to_abi_type_def, is_dynamic_def, IgnAsm `bs = _`] >>
     qpat_x_assum `bs = mem_bytes_at _ _ _` SUBST1_TAC >>
     irule LIST_EQ >>
     simp_tac (srw_ss()) [LENGTH_DROP, LENGTH_mem_bytes_at] >>
     rpt strip_tac >>
     `pos + x < LENGTH bs /\ x + pos < LENGTH bs /\ pos <= LENGTH bs` by decide_tac >>
     asm_simp_tac (srw_ss()) [EL_DROP, EL_mem_bytes_at, LENGTH_mem_bytes_at, ADD_ASSOC] >>
     simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM]) >>
  `B+LENGTH bs <= d \/ d+32 <= B+pos+32` by
    (qhdtm_x_assum `abi_footprint_disjoint` mp_tac >>
     simp[abi_footprint_disjoint_def, type_memory_bytes_def] >> decide_tac) >>
  `!n. n <= maxn ==> {a | d <= a /\ a < d+32+n*type_memory_bytes ce ty} SUBSET
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})` by
    (rpt strip_tac >>
     `n*type_memory_bytes ce ty <= maxn*type_memory_bytes ce ty` by simp[] >>
     simp[type_memory_bytes_def, SUBSET_DEF] >> rpt strip_tac >> disj2_tac >> decide_tac) >>
  `EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi]` by fs[EVERY_DEF] >>
  `fn_has_code st last fn /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_decode_code_context_def, abi_decode_entry_def] >>
  (drule abi_decode_array_bulk_fetched_reentry >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand base_op _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand hi _ = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `decode_site_resources _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `next <= _`)) >>
  disch_then (qspecl_then [
    `scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))}`,
    `w2n (mem_word_at (B+pos) s.vs_memory)`,
    `mem_bytes_at (B+pos) (LENGTH bs-pos) s.vs_memory`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[])) >>
  simp_tac bool_ss [abi_decode_context_result_def] >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`t`, `v`] >>
      asm_simp_tac bool_ss [] >>
      gvs[abi_decode_alloc_progress_def, vyper_to_abi_type_def] >>
      rpt strip_tac >> gvs[]) >>
  disj2_tac >> qexists `u` >> asm_simp_tac bool_ss [])
QED
