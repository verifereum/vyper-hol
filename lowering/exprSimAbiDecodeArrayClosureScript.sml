(* Guard-first initialization and conditional nonbulk array closure. *)
Theory exprSimAbiDecodeArrayClosure
Ancestors
  exprSimAbiDecodeArrayPrepareReentry exprSimAbiDecodeArrayRuntimeSetup
  exprSimAbiDecodeArrayControl exprSimAbiDecodeLabelledLoop
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeArrayInvariant
  exprSimAbiDecodeArrayMembers exprSimAggregateEncoding valueEncodingProps valueEncoding
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeScratchCover
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
