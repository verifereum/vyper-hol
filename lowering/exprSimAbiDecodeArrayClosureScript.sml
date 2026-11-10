(* Guard-first initialization and conditional nonbulk array closure. *)
Theory exprSimAbiDecodeArrayClosure
Ancestors
  loweringStateRelDefs valueEncodingDefs
  abiDecoderArrayLoopInit abiDecoderArrayInit abiDecoderCode abiDecoderRecursiveArray
  abiDecoderDynarrayPrefix fragExec emitHelperProps abiCanonicalHeadSize
  exprSimAbiDecodeWidthBoundary abiDecoderCoherence exprLowering vyperValue
  vyperTypeSystem abiDecoderContract vyperABI contractABI
  exprSimAbiDecodeArrayPrepareReentry exprSimAbiDecodeArrayRuntimeSetup
  exprSimAbiDecodeArrayControl exprSimAbiDecodeLabelledLoop
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeArrayInvariant
  exprSimAbiDecodeArrayMembers exprSimAggregateEncoding valueEncodingProps valueEncoding
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeScratchCover exprSimAbiDecodeSiteProvenance
  exprSimAbiDecodeArraySetup abiDecoderSequenceReach abiDecoderFiniteControl
  abiDecoderIndexInit abiDecoderSiteEffect abiDecoderExecution instIdxIndep
  compileEnv venomState venomInst words list arithmetic finite_map pred_set

Theorem abi_array_index_init_fetched_reentry:
  abi_decode_index_init st = (ip,last) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ abi_decode_entry st s ==>
  ?t slot. Dreach ctx fn s t /\ abi_decode_entry last t /\
    eval_operand ip t = SOME(n2w slot) /\ mload slot t = 0w /\
    fresh_vars_wrt limit_st t /\
    decode_site_effect ctx func st.cs_next_var {a | slot <= a /\ a < slot+32} s t /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME(slot,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (slot = s.vs_alloca_next \/ FLOOKUP s.vs_allocas st.cs_next_id = SOME(slot,32)) /\
    slot + 32 <= t.vs_alloca_next /\ slot < dimword(:256)
Proof
  strip_tac >> drule_all abi_decode_index_init_site_sequence >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_decode_entry_def] >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  qexistsl [`t'`, `p`] >>
  conj_tac >- metis_tac[Dreach_straight_prefix] >>
  gvs[abi_decode_entry_def, eval_op_inst_idx, mload_def,
    fresh_vars_wrt_def, decode_site_effect_inst_idx] >>
  metis_tac[Dreach_straight_prefix]
QED

Theorem abi_array_memory_init_fetched_reentry:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn
    (abi_member_head_size at) st = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w b) /\ eval_operand hi s = SOME(n2w h) /\
  d < dimword(:256) /\ p < dimword(:256) /\ h < dimword(:256) /\ b+h < dimword(:256) /\
  n = w2n (mem_word_at (b+p) s.vs_memory) /\
  bs = mem_bytes_at (b+p) (h-p) s.vs_memory /\ maxn < dimword(:256) /\
  (n <= maxn ==> n*abi_member_head_size at < dimword(:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st header_st fn /\ fn_has_code header_st loop_st fn /\
  abi_decode_entry st s ==>
  (n <= maxn /\ p+32+n*abi_member_head_size at <= h /\
    ?prepared t slot. Dreach ctx fn s prepared /\ Dreach ctx fn prepared t /\
      abi_decode_entry header_st prepared /\ abi_decode_entry loop_st t /\
      eval_operand cnt prepared = SOME(n2w n) /\
      mem_word_at d prepared.vs_memory = n2w n /\
      eval_operand ip t = SOME(n2w slot) /\ mload slot t = 0w /\
      fresh_vars_wrt limit_st t /\
      decode_site_effect ctx func st.cs_next_var {a | d <= a /\ a < d+32} s prepared /\
      decode_site_effect ctx func header_st.cs_next_var
        {a | slot <= a /\ a < slot+32} prepared t /\
      prepared.vs_allocas = s.vs_allocas /\ prepared.vs_alloca_next = s.vs_alloca_next /\
      FLOOKUP t.vs_allocas header_st.cs_next_id = SOME(slot,32) /\
      (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
      (slot = s.vs_alloca_next \/ FLOOKUP s.vs_allocas header_st.cs_next_id = SOME(slot,32)) /\
      slot+32 <= t.vs_alloca_next /\ slot < dimword(:256)) \/
  (?t. Dabort ctx fn s Revert_abort t /\
    ~(vyper_decode_valid_enc (Array NONE at) bs /\
      ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE at) bs) = SOME v))
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decode_dynarray_memory_prepare_fetched_reentry >>
  disch_then (qspecl_then [`ty`, `env`] strip_assume_tac)
  >- (disj1_tac >> asm_rewrite_tac[] >>
      `decode_site_resources ctx func t` by
        metis_tac[decode_site_effect_def] >>
      drule_all abi_array_index_init_fetched_reentry >> strip_tac >>
      qexistsl [`t`, `t'`, `slot`] >> gvs[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem abi_array_memory_prefix_assemble:
  abi_array_memory_prefix tv d m n vs s /\ m = type_memory_size tv /\
  mem_word_at d s.vs_memory = n2w n ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d s.vs_memory
Proof
  simp_tac bool_ss [abi_array_memory_prefix_def, val_in_memory_dynarray] >>
  strip_tac >>
  irule elems_in_memory_intro >> rpt strip_tac >>
  metis_tac[]
QED

Theorem abi_array_source_prefix_assemble:
  abi_array_source_prefix env ty bs p n vs /\
  evaluate_type env ty = SOME tv /\
  n = abi_head_word (DROP p bs) /\ n <= maxn /\
  p+32+n*abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs ==>
  abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) (DROP p bs)
    (ArrayV (make_array_value tv (Dynamic maxn) vs))
Proof
  strip_tac >>
  `32 <= LENGTH (DROP p bs) /\
   32 + abi_head_word (DROP p bs)*abi_member_head_size (vyper_to_abi_type env ty)
     <= LENGTH (DROP p bs)` by (gvs[LENGTH_DROP] >> decide_tac) >>
  `abi_head_word (DROP p bs) <= maxn` by metis_tac[] >>
  drule_all abi_array_dynamic_source >>
  simp_tac bool_ss [abi_array_source_prefix_def] >>
  qpat_x_assum `abi_array_source_prefix _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_array_source_prefix_def] >> metis_tac[]
QED

Theorem abi_array_header_effect_frame:
  decode_site_effect ctx func next V s t /\ decode_protects V {(d,32)} ==>
  mem_word_at d t.vs_memory = mem_word_at d s.vs_memory
Proof
  strip_tac >> drule_all decode_site_effect_mload >>
  simp[mload_def, mem_word_at_def, mem_bytes_at_def]
QED

Theorem abi_array_child_writes_protect_header:
  (!a. d <= a /\ a < d+32+n*m ==> a NOTIN scratch) /\ j < n ==>
  decode_protects (scratch UNION abi_array_cell d m j) {(d,32)}
Proof
  simp[decode_protects_def, abi_array_cell_def] >> rpt strip_tac >>
  `d+32 <= d+32+j*m /\ d+32 <= d+32+n*m` by decide_tac >>
  metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem abi_array_child_effect_header:
  abi_decode_owned outer scratch d (32+n*m) origin /\
  sites SUBSET outer /\ j < n /\
  decode_site_effect ctx func next
    (abi_array_child_scratch sites origin UNION abi_array_cell d m j) s t ==>
  mem_word_at d t.vs_memory = mem_word_at d s.vs_memory
Proof
  strip_tac >> irule abi_array_header_effect_frame >>
  goal_assum (drule_at Any) >>
  irule abi_array_child_writes_protect_header >>
  `abi_array_child_scratch sites origin SUBSET scratch` by
    metis_tac[abi_array_child_scratch_subset, abi_decode_owned_def] >>
  fs[abi_decode_owned_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_array_backedge_header_frame:
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN {a | d <= a /\ a < d+32+n*m}) ==>
  mem_word_at d
    (jump_to hdr (mstore slot w (update_var nv v s))).vs_memory =
  mem_word_at d s.vs_memory
Proof
  strip_tac >>
  `slot+32 <= d \/ d+32 <= slot` by
    (Cases_on `slot+32 <= d` >> simp[] >>
     Cases_on `d+32 <= slot` >> simp[] >>
     first_x_assum (qspec_then `MAX d slot` mp_tac) >>
     simp[MAX_DEF] >> rpt IF_CASES_TAC >> simp[] >> decide_tac) >>
  `mem_bytes_at d 32 (mstore slot w s).vs_memory = mem_bytes_at d 32 s.vs_memory` by
    metis_tac[mstore_mem_bytes_at_disjoint] >>
  fs[mem_word_at_def, mem_bytes_at_def, jump_to_def, mstore_def, update_var_def,
    write_memory_with_expansion_def]
QED

Theorem abi_array_control_header_frame:
  mem_word_at d
    (jump_to lbl (abi_decode_position_header_state base_op hv B p j n s)).vs_memory =
  mem_word_at d s.vs_memory
Proof
  Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_position_header_state_def, jump_to_def, update_var_def]
QED

Theorem abi_array_ready_child_header_frame:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  j < n /\
  decode_site_effect ctx func next
    (abi_array_child_scratch sites origin UNION
     abi_array_cell d (type_memory_bytes ce ty) j) s t ==>
  mem_word_at d t.vs_memory = mem_word_at d s.vs_memory
Proof
  strip_tac >> drule abi_array_ready_loop_data >>
  simp_tac bool_ss [abi_array_loop_data_def] >> strip_tac >>
  irule abi_array_child_effect_header >> metis_tac[]
QED

Theorem abi_array_body_post_backedge_header:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s ==>
  mem_word_at d
    (jump_to hdr (mstore slot w (update_var nv v s))).vs_memory =
  mem_word_at d s.vs_memory
Proof
  simp_tac bool_ss [abi_array_body_post_def, abi_array_loop_data_def] >>
  strip_tac >> irule abi_array_backedge_header_frame >> metis_tac[]
QED

Theorem abi_array_initial_slot_scratch:
  abi_decode_scratch_cover outer scratch s /\ idx IN outer /\
  (slot = s.vs_alloca_next \/ FLOOKUP s.vs_allocas idx = SOME(slot,32)) ==>
  {a | slot <= a /\ a < slot+32} SUBSET scratch
Proof
  simp[abi_decode_scratch_cover_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_array_initial_slot_header:
  abi_decode_owned outer scratch d (32+n*m) origin /\ idx IN outer /\
  (slot = origin.vs_alloca_next \/ FLOOKUP origin.vs_allocas idx = SOME(slot,32)) /\
  decode_site_effect ctx func next {a | slot <= a /\ a < slot+32} s t ==>
  mem_word_at d t.vs_memory = mem_word_at d s.vs_memory
Proof
  strip_tac >>
  `{a | slot <= a /\ a < slot+32} SUBSET scratch` by
    metis_tac[abi_array_initial_slot_scratch, abi_decode_owned_def] >>
  irule abi_array_header_effect_frame >> goal_assum (drule_at Any) >>
  fs[abi_decode_owned_def, decode_protects_def, SUBSET_DEF] >>
  rpt strip_tac >>
  `a < d+(m*n+32)` by decide_tac >> metis_tac[]
QED

Theorem abi_array_owned_init_ready:
  abi_decode_owned sites scratch d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s /\
  abi_decode_context_pre ctx func ce env (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) limit_st next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
    sites st dst src base_op hi B bs pos d s /\
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn a st = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\
  loop_st.cs_next_id <= last.cs_next_id /\
  abi_decode_sites st.cs_next_id last.cs_next_id SUBSET sites /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  abi_decode_bytes_widths env ty /\ type_memory_size tv = type_memory_bytes ce ty /\
  n <= maxn /\ maxn < dimword(:256) /\
  pos+32+n*a <= LENGTH bs /\
  n = w2n(mem_word_at (B+pos) s.vs_memory) /\
  abi_decode_entry loop_st t /\ eval_operand ip t = SOME(n2w slot) /\
  mload slot t = 0w /\ fresh_vars_wrt limit_st t /\
  mem_word_at d prepared.vs_memory = n2w n /\
  decode_site_effect ctx func st.cs_next_var {a | d <= a /\ a < d+32} s prepared /\
  decode_site_effect ctx func header_st.cs_next_var {a | slot <= a /\ a < slot+32} prepared t /\
  prepared.vs_allocas = s.vs_allocas /\ prepared.vs_alloca_next = s.vs_alloca_next /\
  FLOOKUP t.vs_allocas header_st.cs_next_id = SOME(slot,32) /\
  (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (slot = s.vs_alloca_next \/ FLOOKUP s.vs_allocas header_st.cs_next_id = SOME(slot,32)) /\
  slot+32 <= t.vs_alloca_next /\ slot < dimword(:256) ==>
  abi_array_ready ctx func ce env ty tv limit_st next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
    t sites scratch (abi_decode_sites loop_st.cs_next_id last.cs_next_id)
    header_st.cs_next_id slot ip loop_st dst src base_op hi B bs pos d n 0 [] t /\
  mem_word_at d t.vs_memory = n2w n /\
  decode_site_effect ctx func next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))}) s t /\
  abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id) s t
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `header_st.cs_next_id IN sites` by
    (fs[abi_decode_sites_def, SUBSET_DEF] >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  `{a | slot <= a /\ a < slot+32} SUBSET scratch` by
    metis_tac[abi_array_initial_slot_scratch, abi_decode_owned_def] >>
  `next <= st.cs_next_var /\ next <= header_st.cs_next_var` by
    (fs[abi_decode_context_pre_def] >> decide_tac) >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[type_memory_bytes_def] >>
  `decode_site_effect ctx func next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))}) s prepared` by
    (irule decode_site_effect_weaken >>
     qexists `{a | d <= a /\ a < d+32}` >> conj_tac
     >- (simp[SUBSET_DEF] >> rpt strip_tac >> disj2_tac >> simp[] >> decide_tac) >>
     metis_tac[decode_site_effect_threshold]) >>
  `decode_site_effect ctx func next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))}) s t` by
    (irule decode_site_effect_fixed_origin >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists `{a | slot <= a /\ a < slot+32}` >>
     conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >> metis_tac[]) >>
  `abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id) s t` by
    (simp_tac bool_ss [abi_decode_alloc_progress_def] >>
     conj_tac >- metis_tac[decode_site_effect_def] >>
     conj_tac >- metis_tac[decode_site_effect_def] >>
     conj_tac
     >- (simp[abi_decode_sites_def] >> rpt strip_tac >>
         `id <> header_st.cs_next_id` by decide_tac >> metis_tac[]) >>
     rpt strip_tac >>
     `id = header_st.cs_next_id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
     `b = slot /\ sz = 32` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
     gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `abi_decode_alloc_progress sites s t` by
    metis_tac[abi_decode_alloc_progress_widen] >>
  `32+n*type_memory_bytes ce ty <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (simp[type_memory_bytes_def] >> simp[LE_MULT_RCANCEL]) >>
  `abi_decode_owned sites scratch d (32+n*type_memory_bytes ce ty) t` by
    (`abi_decode_owned sites scratch d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t` by
       metis_tac[abi_decode_owned_transport] >>
     qpat_x_assum `abi_decode_owned _ _ _ _ t` mp_tac >>
     simp_tac bool_ss [abi_decode_owned_def] >> strip_tac >>
     conj_tac >- decide_tac >>
     rpt strip_tac >>
     `a' < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by decide_tac >>
     metis_tac[]) >>
  `decode_protects {a | slot <= a /\ a < slot+32} {(d,32)}` by
    (qpat_x_assum `abi_decode_owned _ _ _ _ t` mp_tac >>
     simp_tac bool_ss [abi_decode_owned_def] >> strip_tac >>
     simp_tac (srw_ss()) [decode_protects_def] >> rpt gen_tac >> strip_tac >>
     `a' NOTIN scratch` by
       (qpat_x_assum `!a. d <= a /\ _ ==> a NOTIN scratch` irule >>
        conj_tac >> decide_tac) >>
     qpat_x_assum `{a | slot <= a /\ a < slot+32} SUBSET scratch` mp_tac >>
     simp_tac (srw_ss()) [SUBSET_DEF] >>
     disch_then (qspec_then `a'` mp_tac) >> simp[]) >>
  `mem_word_at d t.vs_memory = mem_word_at d prepared.vs_memory` by
    metis_tac[abi_array_header_effect_frame] >>
  `mem_word_at d t.vs_memory = n2w n` by metis_tac[] >>
  `decode_site_effect ctx func st.cs_next_var
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))}) s t` by
    (`decode_site_effect ctx func st.cs_next_var
       (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))}) s prepared` by
       (irule decode_site_effect_weaken >>
        qexists `{a | d <= a /\ a < d+32}` >> conj_tac
        >- (simp[SUBSET_DEF] >> rpt strip_tac >> disj2_tac >> simp[] >> decide_tac) >>
        first_assum ACCEPT_TAC) >>
     irule decode_site_effect_fixed_origin >>
     qexistsl [`{a | slot <= a /\ a < slot+32}`, `header_st.cs_next_var`, `prepared`] >>
     conj_tac >- decide_tac >>
     conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_array_runtime_context ctx func ce env ty tv limit_st next scratch
    (abi_decode_sites loop_st.cs_next_id last.cs_next_id)
    loop_st dst src base_op hi B bs pos d n t` by
    (qpat_x_assum `abi_decode_context_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decode_context_pre_def] >> strip_tac >>
     `eval_operand dst t = SOME(n2w d) /\ eval_operand src t = SOME(n2w pos) /\
      eval_operand base_op t = SOME(n2w B) /\ eval_operand hi t = SOME(n2w(LENGTH bs))` by
       (qpat_x_assum `decode_site_effect _ _ st.cs_next_var _ s t` mp_tac >>
        simp_tac bool_ss [decode_site_effect_def] >> strip_tac >>
        fs[EVERY_DEF] >> metis_tac[]) >>
     `bs = mem_bytes_at B (LENGTH bs) t.vs_memory` by
       (qpat_x_assum `decode_site_effect _ _ next _ s t` mp_tac >>
        simp_tac bool_ss [decode_site_effect_def, decode_memory_frame_def] >>
        strip_tac >> metis_tac[]) >>
     `s.vs_alloca_next <= t.vs_alloca_next /\ decode_site_resources ctx func t` by
       metis_tac[decode_site_effect_def] >>
     `abi_decode_sites loop_st.cs_next_id last.cs_next_id SUBSET sites` by
       (fs[abi_decode_sites_def, SUBSET_DEF] >> rpt strip_tac >>
        first_x_assum irule >> simp[] >> decide_tac) >>
     `assignable_type env ty` by fs[assignable_type_def] >>
     `next <= loop_st.cs_next_var /\ st.cs_next_var <= loop_st.cs_next_var /\
      pos+32 <= LENGTH bs /\ d+32+n*type_memory_bytes ce ty < dimword(:256) /\
      B+LENGTH bs <= t.vs_alloca_next` by decide_tac >>
     `EVERY (abi_decoder_operand_live loop_st.cs_next_var) [dst;src;base_op;hi]` by
       (qpat_x_assum `EVERY (abi_decoder_operand_live _) [dst;src;base_op;hi]` mp_tac >>
        simp_tac bool_ss [EVERY_DEF] >> strip_tac >> rpt conj_tac >>
        irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
        qexists `st.cs_next_var` >> conj_tac >> first_assum ACCEPT_TAC) >>
     `!id b sz. id IN abi_decode_sites loop_st.cs_next_id last.cs_next_id /\
       FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
       abi_footprint_disjoint B (LENGTH bs) [(b,sz)]` by
       (rpt strip_tac >> `id <> header_st.cs_next_id` by
          (fs[abi_decode_sites_def] >> decide_tac) >>
        `FLOOKUP s.vs_allocas id = SOME(b,sz) /\ id IN sites` by
          metis_tac[SUBSET_DEF] >> metis_tac[]) >>
     asm_simp_tac bool_ss [abi_array_runtime_context_def] >>
     reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
     qpat_x_assum `!a. B <= a /\ _ ==> a NOTIN _` (qspec_then `a'` mp_tac) >>
     gvs[IN_UNION, GSPECIFICATION] >> decide_tac) >>
  `decode_protects
     (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
     {(B+pos,32)}` by
    (qpat_x_assum `abi_decode_context_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decode_context_pre_def] >> strip_tac >>
     simp[decode_protects_def, IN_UNION, GSPECIFICATION] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `mload (B+pos) t = mload (B+pos) s` by
    metis_tac[decode_site_effect_mload] >>
  `mem_word_at (B+pos) t.vs_memory = mem_word_at (B+pos) s.vs_memory` by
    fs[mload_def, mem_word_at_def] >>
  `abi_decoder_operand_live loop_st.cs_next_var ip` by
    (simp [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, IN_GSPEC] >>
     rpt strip_tac >> irule fresh_var_distinct >> decide_tac) >>
  `!a. slot <= a /\ a < slot+32 ==>
    a NOTIN {a | d <= a /\ a < d+32+n*type_memory_bytes ce ty}` by
    (qpat_x_assum `abi_decode_owned sites scratch d (32 + n * _) t` mp_tac >>
     simp_tac bool_ss [abi_decode_owned_def] >> strip_tac >>
     fs[SUBSET_DEF, GSPECIFICATION] >> rpt strip_tac >> metis_tac[ADD_ASSOC, ADD_COMM]) >>
  `abi_decode_sites loop_st.cs_next_id last.cs_next_id SUBSET sites` by
    (fs[abi_decode_sites_def, SUBSET_DEF] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  qpat_assum `abi_array_runtime_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_array_runtime_context_def] >> strip_tac >>
  `alloca_inv t` by metis_tac[actualDecoderSitesTheory.decode_site_resources_def] >>
  asm_simp_tac bool_ss [abi_array_ready_def, abi_array_loop_data_def,
    abiDecoderLoopDataTheory.Ldata_def, abi_array_source_prefix_def, abi_array_memory_prefix_def] >>
  simp[decode_site_effect_refl, abi_decode_alloc_progress_def,
    abi_decode_sites_def, abi_decode_load_def, w2n_n2w] >>
  simp[mload_def, mem_word_at_def] >> rpt strip_tac >> gvs[]
QED

Theorem abi_decode_owned_dynamic_array_nonbulk:
  abi_decode_owned_child_contract ce env ty tv /\
  evaluate_type env ty = SOME tv /\
  type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info ce.ce_struct_fields ce ty) a m dyn maxn /\
  (dyn \/ dec_info_needs_clamp (type_to_abi_dec_info ce.ce_struct_fields ce ty)) ==>
  abi_decode_owned_child_contract ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  simp_tac bool_ss [abi_decode_owned_child_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray (type_to_abi_dec_info ce.ce_struct_fields ce ty) a m dyn maxn) st = ((),last)` by metis_tac[] >>
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  fs[abi_decode_context_pre_def] >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` by
    fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `a = abi_member_head_size (vyper_to_abi_type env ty) /\
   m = type_memory_bytes ce ty /\ dyn = is_dynamic (vyper_to_abi_type env ty)` by
    fs[type_to_abi_dec_info_def] >>
  `maxn < dimword(:256)` by
    (qpat_x_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` mp_tac >>
     simp_tac bool_ss [abi_decoder_coherent_array_iff, abi_decoder_header_def] >>
     strip_tac >> fs[Once evaluate_type_def, type_slot_size_def, AllCaseEqs()] >>
     `maxn <= maxn * type_slot_size tv` by
       (simp[LE_MULT_CANCEL_LBARE] >> decide_tac) >> decide_tac) >>
  `assignable_type env ty` by fs[assignable_type_def] >>
  `abi_embedded_static_size ce.ce_struct_fields ty <= type_memory_bytes ce ty` by
    metis_tac[abi_decode_embedded_head_le_memory] >>
  `!n. n <= maxn ==> n*abi_member_head_size (vyper_to_abi_type env ty) < dimword(:256)` by
    (rpt strip_tac >>
     `n*abi_member_head_size (vyper_to_abi_type env ty) <= maxn*type_memory_bytes ce ty` by
       (irule LESS_MONO_MULT2 >> metis_tac[]) >>
     fs[type_memory_bytes_def] >> decide_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decoder_recursive_loop_end >> strip_tac >>
  `cs_extends st loop_st` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code st last fn` by fs[abi_decode_code_context_def] >>
  `fn_has_code st loop_st fn /\ fn_has_code loop_st last fn` by
    metis_tac[fn_has_code_split] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
  `cs_extends st header_st /\ cs_extends header_st loop_st` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code st header_st fn /\ fn_has_code header_st loop_st fn` by
    metis_tac[fn_has_code_split] >>
  `MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func)` by
    (irule abi_decode_index_init_registered_instruction >>
     goal_assum (drule_at Any) >> fs[abi_decode_code_context_def] >> metis_tac[]) >>
  `d < dimword(:256) /\ LENGTH bs < dimword(:256) /\
   loop_st.cs_next_var <= limit_st.cs_next_var` by
    (fs[type_memory_bytes_def] >> decide_tac) >>
  `abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn
    (abi_member_head_size (vyper_to_abi_type env ty)) st = (addr,guard_st)` by metis_tac[] >>
  qabbrev_tac `n = w2n (mem_word_at (B+pos) s.vs_memory)` >>
  qabbrev_tac `suffix = mem_bytes_at (B+pos) (LENGTH bs-pos) s.vs_memory` >>
  `n = w2n (mem_word_at (B+pos) s.vs_memory) /\
   suffix = mem_bytes_at (B+pos) (LENGTH bs-pos) s.vs_memory` by
    simp[Abbr `n`, Abbr `suffix`] >>
  `(n <= maxn ==> n*abi_member_head_size (vyper_to_abi_type env ty) < dimword(:256))` by
    metis_tac[] >>
  `suffix = DROP pos bs` by
    (Cases_on `pos <= LENGTH bs`
     >- (qspec_then `B` (qspec_then `pos` (qspec_then `LENGTH bs-pos` mp_tac))
           mem_bytes_at_window >>
         disch_then (qspec_then `LENGTH bs` (qspec_then `s.vs_memory` mp_tac)) >>
         qpat_assum `bs = mem_bytes_at _ _ _` (fn th => rewrite_tac[GSYM th]) >>
         simp[Abbr `suffix`, TAKE_LENGTH_TOO_LONG]) >>
     `LENGTH bs-pos = 0 /\ LENGTH bs <= pos` by decide_tac >>
     simp[Abbr `suffix`, mem_bytes_at_def, DROP_EQ_NIL]) >>
  drule_all abi_array_memory_init_fetched_reentry >>
  disch_then (qspecl_then [`ty`, `env`]
    (DISJ_CASES_THEN2 strip_assume_tac
      (fn th => strip_assume_tac th >>
        simp_tac bool_ss [abi_decode_context_result_def] >> disj2_tac >>
        qexists_tac `t` >>
        (conj_tac >- first_assum ACCEPT_TAC >>
         qpat_x_assum `~(_ /\ ?v. _)` mp_tac >>
         qpat_assum `suffix = DROP pos bs` SUBST1_TAC >>
         simp_tac std_ss [abi_decode_source_accepts_def, abi_decode_source_view_def,
           vyper_to_abi_type_def, is_dynamic_def, GSYM LEFT_EXISTS_AND_THM] >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[])))) >>
  `abi_decode_context_pre ctx func ce env (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) limit_st next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
    sites st dst src base_op hi B bs pos d s` by
      (simp[abi_decode_context_pre_def, EVERY_DEF] >> metis_tac[]) >>
  `abi_array_ready ctx func ce env ty tv limit_st next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
    t sites scratch (abi_decode_sites loop_st.cs_next_id last.cs_next_id)
    header_st.cs_next_id slot ip loop_st dst src base_op hi B bs pos d n 0 [] t /\
   mem_word_at d t.vs_memory = n2w n /\
   decode_site_effect ctx func next
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))}) s t /\
   abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id) s t` by
    (irule abi_array_owned_init_ready >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qexistsl_tac [`abi_member_head_size (vyper_to_abi_type env ty)`,
          `addr`, `cnt`, `guard_st`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- metis_tac[] >>
     conj_tac >-
       (qpat_x_assum `abi_decode_bytes_widths env (ArrayT ty (Dynamic maxn))` mp_tac >>
        simp[abi_decode_bytes_widths_def]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qexists_tac `prepared` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  (drule_all abiDecoderRecursiveLoopEntryTheory.abi_decoder_recursive_entry_code >> strip_tac >>
   `Dreach ctx fn t
      (jump_to (fresh_label_output "dec_dyn_hdr" loop_st.cs_next_label) t)` by
     (irule Dreach_edge >> simp_tac bool_ss [Dedge_def] >> disj2_tac >>
      conj_tac >- fs[abi_decode_entry_def] >>
      qexistsl_tac [`bb`, `hdr_bb`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- metis_tac[abi_decode_entry_def] >>
      conj_tac >-
        (gen_tac >>
         irule abiDecoderPrimitiveLoopEntryTheory.abi_decoder_loop_entry_control >>
         conj_tac >- metis_tac[abi_decode_entry_def] >>
         qexistsl_tac [`loop_st.cs_next_id`, `loop_st.cs_current_insts`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         metis_tac[abi_decode_entry_def]) >>
      simp[jump_to_def] >> metis_tac[abi_decode_entry_def]) >>
   qmatch_asmsub_abbrev_tac `Dreach ctx fn t (jump_to hdr t)` >>
   qabbrev_tac `header = loop_st with <|cs_current_bb := hdr; cs_current_insts := []|>` >>
   `abi_array_ready ctx func ce env ty tv limit_st next
      (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
      t sites scratch (abi_decode_sites loop_st.cs_next_id last.cs_next_id)
      header_st.cs_next_id slot ip header dst src base_op hi B bs pos d n 0 []
      (jump_to hdr t)` by
     (irule abi_array_ready_jump_transport >>
      simp_tac (srw_ss()) [Abbr `header`] >>
      qexists `loop_st` >> simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
   drule abiDecoderLoopEmitTheory.abi_decode_dyn_loop_trace >> strip_tac >>
   drule abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_prefix_facts >> strip_tac >>
   drule abiDecoderArraySetupCodeTheory.abi_decoder_array_setup_head >> strip_tac >>
   drule abiDecoderAppendTheory.cs_extends_abi_decode >> strip_tac >>
   `?children. st1.cs_blocks = children ++ middle.cs_blocks` by
     (qpat_x_assum `cs_extends middle st1` mp_tac >>
      pure_rewrite_tac [cs_extends_def] >> strip_tac >>
      goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
   qpat_assum `FST ops = Var _` (fn head =>
     qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _`
       (mp_tac o PURE_REWRITE_RULE [head])) >> strip_tac >>
   drule abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_suffix_facts >> strip_tac >>
   `st.cs_blocks <> last.cs_blocks` by
     (disch_then (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >>
      asm_simp_tac (srw_ss()) [LENGTH_APPEND] >> decide_tac) >>
   `!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
         phi_prefix_length bb.bb_instructions = 0` by
      (fs[abi_decode_code_context_def] >> metis_tac[]) >>
   drule_all abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_phase_cfg >> strip_tac >>
   `header.cs_current_bb = FST labels /\ header.cs_current_insts = []` by
     (qpat_x_assum `abi_decode_loop_prefix _ _ _ _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [abiDecoderLoopEmitTheory.abi_decode_loop_prefix_shape,
        Abbr `header`, Abbr `hdr`] >> strip_tac >>
      qpat_x_assum `(_,_,_) = labels` (SUBST1_TAC o SYM) >> simp_tac (srw_ss()) []) >>
   `src <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
    base_op <> Var (STRING #"%" (toString loop_st.cs_next_var))` by
     (conj_tac >> strip_tac >>
      gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
          abiDecoderReentryTheory.abi_decoder_older_vars_def] >>
      first_x_assum (qspec_then `loop_st.cs_next_var` mp_tac) >> simp[]) >>
   qabbrev_tac `Ready = \j h. ?vs.
     abi_array_ready ctx func ce env ty tv limit_st next
       (scratch UNION {a | d <= a /\ a < d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
       t sites scratch (abi_decode_sites loop_st.cs_next_id last.cs_next_id)
       header_st.cs_next_id slot ip header dst src base_op hi B bs pos d n j vs h /\
     mem_word_at d h.vs_memory = n2w n` >>
   qabbrev_tac `H = \j h. jump_to (if j < n then st0.cs_current_bb else SND (SND labels))
     (abi_decode_position_header_state base_op loop_st.cs_next_var B pos j n h)` >>
   qabbrev_tac `Done = \u. ?h'. Ready n h' /\ u = H n h'` >>
   `!j h. Ready j h ==>
     ((?u. Dabort ctx fn h Revert_abort u /\
       ~(vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) (DROP pos bs) /\
         ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
           (dec (Array NONE (vyper_to_abi_type env ty)) (DROP pos bs)) = SOME v)) \/
      (?u. Dreach ctx fn h u /\ Done u))` by
     (ho_match_mp_tac (Q.INST [`H` |-> `H`, `n` |-> `n`] decoder_finite_loop_labelled) >>
      conj_tac >-
        (rpt gen_tac >> simp_tac bool_ss [Abbr `Ready`] >> strip_tac >>
         drule abi_array_ready_position_ready >>
         simp_tac (srw_ss()) [Abbr `header`] >>
         pure_rewrite_tac [abi_decode_position_loop_ready_def] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >-
        (rpt gen_tac >> strip_tac >> conj_tac
         >- (qpat_x_assum `Ready j h` mp_tac >>
             simp_tac bool_ss [Abbr `Ready`] >> strip_tac >>
             simp_tac bool_ss [Abbr `H`] >>
             `abi_decode_position_loop_cfg fn header.cs_current_bb st0.cs_current_bb
                (SND (SND labels)) (loop_st.cs_next_id+1) ip src MLOAD base_op
                loop_st.cs_next_var` by
               (qpat_assum `header.cs_current_bb = FST labels`
                  (fn eq => pure_rewrite_tac [eq]) >> first_assum ACCEPT_TAC) >>
             drule_all abi_array_ready_header_reach >> strip_tac >>
             first_assum ACCEPT_TAC) >>
         strip_tac >> simp_tac bool_ss [Abbr `Done`] >>
         qexists `h` >> simp_tac bool_ss [] >>
         qpat_x_assum `j = n` SUBST_ALL_TAC >>
         simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `Ready j h` mp_tac >>
      simp_tac bool_ss [Abbr `Ready`] >> strip_tac >>
      `st0.cs_next_var <= middle.cs_next_var` by
        (drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      `middle.cs_next_var <= st1.cs_next_var` by
        (drule abiDecoderCountersTheory.abi_decoder_variable_counter >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      `EVERY (abi_decoder_operand_live st0.cs_next_var) [dst;src;base_op;hi;ip]` by
        (`st.cs_next_var <= st0.cs_next_var /\ loop_st.cs_next_var <= st0.cs_next_var` by decide_tac >>
         `abi_decoder_operand_live loop_st.cs_next_var ip` by
           (qpat_assum `ip = _` (fn eq => pure_rewrite_tac [eq]) >>
            simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
              abiDecoderReentryTheory.abi_decoder_older_vars_def]) >>
         simp_tac list_ss [EVERY_DEF] >> rpt conj_tac >>
         metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono]) >>
      `abi_array_ready ctx func ce env ty tv limit_st next
        (scratch UNION {a | d <= a /\ a < d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
        t sites scratch (abi_decode_sites loop_st.cs_next_id last.cs_next_id)
        header_st.cs_next_id slot ip st0 dst src base_op hi B bs pos d n j vs (H j h)` by
        (simp_tac bool_ss [Abbr `H`] >>
         qpat_assum `j < n` (fn lt => pure_rewrite_tac [lt, COND_CLAUSES]) >>
         irule abi_array_ready_header_transport >>
         conj_tac >- decide_tac >>
         conj_tac >- decide_tac >>
         conj_tac >- decide_tac >>
         conj_tac >- simp_tac bool_ss [] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexists `header` >>
         conj_tac >- simp_tac (srw_ss()) [Abbr `header`] >>
         first_assum ACCEPT_TAC) >>
      drule_all abiDecoderLoopCodeTheory.abi_decoder_loop_phase_containment >> strip_tac >>
      drule_all abiDecoderArraySetupCodeTheory.abi_decoder_array_body_code >> strip_tac >>
      drule_all abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_phase_lookups >> strip_tac >>
      `abi_decode_code_context func fn middle st1` by
        (qpat_assum `abi_decode_code_context func fn st last` mp_tac >>
         simp_tac bool_ss [abi_decode_code_context_def] >> strip_tac >>
         conj_tac >- first_assum ACCEPT_TAC >>
         strip_tac >> disj2_tac >> rpt strip_tac >>
         qpat_assum `lookup_block st1.cs_current_bb fn.fn_blocks = SOME _`
           (fn eq => fs[eq]) >>
         gvs[abiDecoderExecutionTheory.abi_decode_backedge_insts_def,
             venomExecSemanticsTheory.phi_prefix_length_def, mk_inst_def]) >>
      `abi_decode_sites middle.cs_next_id st1.cs_next_id SUBSET
        abi_decode_sites loop_st.cs_next_id last.cs_next_id` by
        (simp_tac (srw_ss()) [abi_decode_sites_def, SUBSET_DEF] >> rpt strip_tac >> decide_tac) >>
      `middle.cs_next_var <= limit_st.cs_next_var /\ st1.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
      drule_all abi_array_ready_child_envelope >> strip_tac >>
      `n * type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty` by
        (simp_tac (srw_ss()) [LE_MULT_RCANCEL] >> decide_tac) >>
      `(abi_array_child_scratch (abi_decode_sites loop_st.cs_next_id last.cs_next_id) t UNION
        abi_array_cell d (type_memory_bytes ce ty) j) SUBSET
        (scratch UNION {a | d <= a /\ a < d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))})` by
        (irule SUBSET_TRANS >>
         qexists `scratch UNION {a | d <= a /\ a < d+32+n*type_memory_bytes ce ty}` >>
         conj_tac >- first_assum ACCEPT_TAC >>
         simp_tac (srw_ss()) [SUBSET_DEF, type_memory_bytes_def] >>
         rpt strip_tac >> simp[] >> decide_tac) >>
      `(?t' v. Dreach ctx fn (H j h) t' /\
         abi_decode_source_accepts env ty
           (abi_array_member_view (vyper_to_abi_type env ty) bs pos j) v /\
         val_in_memory tv v (d+32+j*type_memory_bytes ce ty) t'.vs_memory /\
         decode_site_effect ctx func st0.cs_next_var
           (abi_array_child_scratch (abi_decode_sites loop_st.cs_next_id last.cs_next_id) t UNION
            abi_array_cell d (type_memory_bytes ce ty) j) (H j h) t' /\
         abi_decode_alloc_progress (abi_decode_sites loop_st.cs_next_id last.cs_next_id) (H j h) t' /\
         abi_array_body_post ctx func ce env ty tv limit_st next
           (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
           t sites scratch (abi_decode_sites loop_st.cs_next_id last.cs_next_id)
           header_st.cs_next_id slot ip st1 dst src base_op hi B bs pos d n j (vs ++ [v]) t' /\
         eval_operand (FST ops) t' = SOME(n2w j)) \/
       (?u. Dabort ctx fn (H j h) Revert_abort u /\
         ~(?v. abi_decode_source_accepts env ty
           (abi_array_member_view (vyper_to_abi_type env ty) bs pos j) v))` by
        (Cases_on `is_dynamic (vyper_to_abi_type env ty)`
         >- (`dec_info_needs_offset (type_to_abi_dec_info ce.ce_struct_fields ce ty)` by
               (drule abiDecoderOffsetTheory.abi_decoder_array_child_offset >>
                disch_then (fn eq => pure_rewrite_tac [eq]) >> first_assum ACCEPT_TAC) >>
             `!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem` by
               (drule abi_decoder_coherent_header >>
                simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
                drule_all assignable_type_slot_size_pos >> strip_tac >>
                metis_tac[abiDecoderHeadAdequacyTheory.evaluated_positive_type_excludes_empty_abi_array]) >>
             `abi_decode_array_element_setup ip src dst MLOAD base_op hi
                (type_to_abi_dec_info ce.ce_struct_fields ce ty) 32
                (type_memory_bytes ce ty) st0 = (ops,middle)` by
               (qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ st0 = _` mp_tac >>
                qpat_assum `a = _` (fn eq => pure_rewrite_tac [eq]) >>
                qpat_assum `m = _` (fn eq => pure_rewrite_tac [eq]) >>
                simp[abiDecodeRangesTheory.abi_member_head_size_def]) >>
             drule_all abi_array_ready_dynamic_body_outcome >> disch_then ACCEPT_TAC) >>
         `~dec_info_needs_offset (type_to_abi_dec_info ce.ce_struct_fields ce ty)` by
           (drule abiDecoderOffsetTheory.abi_decoder_array_child_offset >>
            disch_then (fn eq => pure_rewrite_tac [eq]) >> first_assum ACCEPT_TAC) >>
         `abi_decode_array_element_setup ip src dst MLOAD base_op hi
            (type_to_abi_dec_info ce.ce_struct_fields ce ty)
            (abi_member_head_size (vyper_to_abi_type env ty))
            (type_memory_bytes ce ty) st0 = (ops,middle)` by metis_tac[] >>
         drule_all abi_array_ready_static_body_outcome >> disch_then ACCEPT_TAC) >>
      all_tac
      >- (drule_all abi_array_ready_child_header_frame >> strip_tac >>
          `eval_operand (Var (STRING #"%" (toString st0.cs_next_var))) t' = SOME(n2w j)` by metis_tac[] >>
          `ip <> Var (STRING #"%" (toString st1.cs_next_var))` by
            (strip_tac >>
             gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
                 abiDecoderReentryTheory.abi_decoder_older_vars_def] >>
             first_x_assum (qspec_then `st1.cs_next_var` mp_tac) >> simp[]) >>
          `phi_prefix_length (abi_decode_position_header_insts (loop_st.cs_next_id+1)
            ip src MLOAD base_op loop_st.cs_next_var st0.cs_current_bb (SND (SND labels))) = 0` by
            (simp[abiDecoderExecutionTheory.abi_decode_position_header_insts_def,
              venomExecSemanticsTheory.phi_prefix_length_def, mk_inst_def]) >>
          `Dreach ctx fn t'
            (jump_to (FST labels) (mstore slot (n2w(SUC j))
              (update_var (STRING #"%" (toString st1.cs_next_var)) (n2w(SUC j)) t')))` by
            (irule abi_array_body_post_backedge_reach >>
             simp_tac (srw_ss()) [] >>
             conj_tac
             >- (goal_assum (drule_at Any) >> simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
             goal_assum (drule_at Any) >>
             simp_tac (srw_ss()) [] >>
             goal_assum (drule_at Any) >> simp_tac (srw_ss()) [] >>
             goal_assum (drule_at Any) >> simp_tac (srw_ss()) [] >>
             goal_assum (drule_at Any) >> simp_tac (srw_ss()) [] >>
             qexists `st1.cs_next_id` >> simp[]) >>
          disj2_tac >>
          qexists `jump_to (FST labels) (mstore slot (n2w(SUC j))
            (update_var (STRING #"%" (toString st1.cs_next_var)) (n2w(SUC j)) t'))` >>
          conj_tac >- metis_tac[Dreach_trans] >>
          qexists `vs ++ [v]` >> conj_tac
          >- (irule abi_array_body_post_backedge_ready >>
              goal_assum (drule_at Any) >>
              simp_tac (srw_ss()) [Abbr `header`] >>
              conj_tac >- decide_tac >>
              conj_tac >- decide_tac >>
              conj_tac >- decide_tac >>
              conj_tac >- (qpat_x_assum `_ .cs_current_bb = FST labels` mp_tac >>
                simp[]) >>
              conj_tac
              >- (`abi_decoder_operand_live loop_st.cs_next_var ip` by
                    (qpat_assum `ip = _` (fn eq => pure_rewrite_tac [eq]) >>
                     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
                       abiDecoderReentryTheory.abi_decoder_older_vars_def]) >>
                  rpt conj_tac >>
                  metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono]) >>
              conj_tac
              >- (irule abi_array_index_outer_site >>
                  qexistsl [`st`,`ip`,`last`,`loop_st`] >>
                  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
                  simp[] >> decide_tac) >>
              qexists `st1` >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
          drule abi_array_body_post_backedge_header >>
          disch_then (fn th => pure_rewrite_tac [th]) >>
          simp_tac (srw_ss()) [Abbr `H`, abi_decode_position_header_state_def,
            jump_to_def, update_var_def] >>
          qpat_x_assum `mem_word_at d t'.vs_memory = _` mp_tac >>
          simp_tac (srw_ss()) [abi_decode_position_header_state_def,
            jump_to_def, update_var_def] >>
          disch_then SUBST1_TAC >>
          simp_tac (srw_ss()) [LET_THM, update_var_def] >>
          qpat_assum `base_op <> Lit 0w` (fn th => pure_rewrite_tac [th, COND_CLAUSES]) >>
          simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
      disj1_tac >> qexists `u` >> conj_tac >- first_assum ACCEPT_TAC >>
      `TAKE 32 (DROP pos bs) = mem_bytes_at (B+pos) 32 s.vs_memory` by
        (qpat_assum `bs = mem_bytes_at B (LENGTH bs) s.vs_memory`
           (fn th => once_rewrite_tac [th]) >>
         irule mem_bytes_at_window >> decide_tac) >>
      `abi_head_word (DROP pos bs) = n` by
        (pure_rewrite_tac [abi_head_word_def] >>
         qpat_x_assum `TAKE 32 (DROP pos bs) = _` (fn th => pure_rewrite_tac [th]) >>
         simp[Abbr `n`, mem_word_at_def, mem_bytes_at_def]) >>
      `~(?v. abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) (DROP pos bs) v)` by
        (irule abi_array_dynamic_member_reject >> qexists `j` >>
         conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
      qpat_x_assum `~(?v. abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) _ v)` mp_tac >>
      pure_rewrite_tac [abi_decode_source_accepts_def, vyper_to_abi_type_def] >>
      POP_ASSUM_LIST (K (metis_tac[]))) >>
   `Ready 0 (jump_to hdr t)` by
     (simp_tac bool_ss [Abbr `Ready`] >> qexists `[]` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp_tac (srw_ss()) [jump_to_def] >> first_assum ACCEPT_TAC) >>
   qpat_x_assum `!j h. Ready j h ==> _`
     (qspecl_then [`0`, `jump_to hdr t`] mp_tac) >>
   impl_tac >- first_assum ACCEPT_TAC >>
   disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)
   >- (simp_tac bool_ss [abi_decode_context_result_def] >> disj2_tac >>
       qexists `u` >> conj_tac
       >- (irule Dreach_abort >> qexists `t` >> conj_tac
           >- (irule Dreach_trans >> qexists `prepared` >>
               conj_tac >> first_assum ACCEPT_TAC) >>
           irule Dreach_abort >> qexists `jump_to hdr t` >>
           conj_tac >> first_assum ACCEPT_TAC) >>
       qpat_x_assum `~(_ /\ ?v. _)` mp_tac >>
       pure_rewrite_tac [abi_decode_source_accepts_def, abi_decode_source_view_def,
         vyper_to_abi_type_def, is_dynamic_def] >>
       simp_tac std_ss [] >>
       POP_ASSUM_LIST (K (metis_tac[]))) >>
   qpat_x_assum `Done u` mp_tac >> simp_tac bool_ss [Abbr `Done`] >>
   disch_then (qx_choose_then `hfinal` strip_assume_tac) >>
   qpat_x_assum `Ready n hfinal` mp_tac >>
   simp_tac bool_ss [Abbr `Ready`] >> strip_tac >>
   drule abi_array_ready_exit_observations >> strip_tac >>
   `abi_array_source_prefix env ty bs pos n vs /\
    abi_array_memory_prefix tv d (type_memory_bytes ce ty) n vs (H n hfinal)` by
     (simp_tac bool_ss [Abbr `H`] >>
      drule abi_array_ready_exit_prefix >> strip_tac >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `!hv exit_lbl. _`
        (qspecl_then [`loop_st.cs_next_var`,
          `if n < n then st0.cs_current_bb else SND (SND labels)`] mp_tac) >>
      simp_tac bool_ss [] >> strip_tac >> first_assum ACCEPT_TAC) >>
   `mem_word_at d (H n hfinal).vs_memory = n2w n` by
     (simp_tac bool_ss [Abbr `H`] >>
      simp_tac arith_ss [] >>
      qpat_assum `mem_word_at d hfinal.vs_memory = _`
        (fn eq => pure_rewrite_tac [GSYM eq]) >>
      irule abi_array_control_header_frame) >>
   `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
      d (H n hfinal).vs_memory` by
     (irule abi_array_memory_prefix_assemble >>
      qexistsl [`type_memory_bytes ce ty`, `n`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
   `TAKE 32 (DROP pos bs) = mem_bytes_at (B+pos) 32 s.vs_memory` by
     (qpat_assum `bs = mem_bytes_at B (LENGTH bs) s.vs_memory`
        (fn th => once_rewrite_tac [th]) >>
      irule mem_bytes_at_window >> decide_tac) >>
   `n = abi_head_word (DROP pos bs)` by
     (pure_rewrite_tac [abi_head_word_def] >>
      qpat_x_assum `TAKE 32 (DROP pos bs) = _` (fn th => pure_rewrite_tac [th]) >>
      simp[Abbr `n`, mem_word_at_def, mem_bytes_at_def]) >>
   `abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) (DROP pos bs)
      (ArrayV (make_array_value tv (Dynamic maxn) vs))` by
     (irule abi_array_source_prefix_assemble >>
      conj_tac >- first_assum ACCEPT_TAC >> qexists `n` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- decide_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
   `st0.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= st1.cs_next_var` by
     (drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
      strip_tac >> drule abiDecoderCountersTheory.abi_decoder_variable_counter >>
      strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
   `decode_site_resources ctx func hfinal` by
     metis_tac[decode_site_effect_def] >>
   `decode_site_effect ctx func next
      (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
      hfinal (H n hfinal) /\ fresh_vars_wrt limit_st (H n hfinal) /\
    (!op. abi_decoder_operand_live loop_st.cs_next_var op ==>
       eval_operand op (H n hfinal) = eval_operand op hfinal)` by
     (simp_tac bool_ss [Abbr `H`] >> irule abi_array_header_effect >>
      conj_tac >- decide_tac >> conj_tac >- decide_tac >>
      conj_tac >> first_assum ACCEPT_TAC) >>
   `decode_site_effect ctx func next
      (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))})
      s (H n hfinal)` by
     (metis_tac[decode_site_effect_trans, UNION_IDEMPOT]) >>
   `Dreach ctx fn s (H n hfinal)` by
     (irule Dreach_trans >> qexists `prepared` >> conj_tac
      >- first_assum ACCEPT_TAC >>
      irule Dreach_trans >> qexists `t` >> conj_tac
      >- first_assum ACCEPT_TAC >>
      irule Dreach_trans >> qexists `jump_to hdr t` >>
      conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]) >>
   `(H n hfinal).vs_allocas = hfinal.vs_allocas /\
    (H n hfinal).vs_alloca_next = hfinal.vs_alloca_next` by
     (Cases_on `base_op = Lit 0w` >>
      simp[Abbr `H`, abi_decode_position_header_state_def, jump_to_def, update_var_def]) >>
   `abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id)
      t (H n hfinal)` by
     (irule abi_decode_alloc_progress_widen >>
      qexists `abi_decode_sites loop_st.cs_next_id last.cs_next_id` >> conj_tac
      >- (simp[abi_decode_sites_def, SUBSET_DEF] >> decide_tac) >>
      (qpat_x_assum `abi_decode_alloc_progress _ t hfinal` mp_tac >>
          simp_tac bool_ss [abi_decode_alloc_progress_def] >>
          qpat_assum `(H n hfinal).vs_allocas = _`
            (fn th => pure_rewrite_tac [th]) >>
          qpat_assum `(H n hfinal).vs_alloca_next = _`
            (fn th => pure_rewrite_tac [th]) >> simp_tac bool_ss [])) >>
   `abi_decode_alloc_progress (abi_decode_sites st.cs_next_id last.cs_next_id)
      s (H n hfinal)` by metis_tac[abi_decode_alloc_progress_trans] >>
   `abi_decode_entry last (H n hfinal)` by
     (simp[abi_decode_entry_def, Abbr `H`, jump_to_def,
        abi_decode_position_header_state_def, update_var_def]) >>
   simp_tac bool_ss [abi_decode_context_result_def] >> disj1_tac >>
   qexistsl [`H n hfinal`, `ArrayV (DynArrayV vs)`] >>
   rpt (conj_tac >- first_assum ACCEPT_TAC) >>
   conj_tac
   >- (qpat_x_assum `abi_decode_source_accepts _ _ (DROP pos bs) _` mp_tac >>
       pure_rewrite_tac [abi_decode_source_view_def, is_dynamic_def, make_array_value_def] >>
       simp_tac std_ss []) >>
   rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC)
QED

