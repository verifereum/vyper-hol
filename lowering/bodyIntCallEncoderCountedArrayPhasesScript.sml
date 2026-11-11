(* Physical array phases on their counted execution endpoints. *)
Theory bodyIntCallEncoderCountedArrayPhases
Ancestors
  bodyIntCallEncoderCountedPhases bodyIntCallEncoderCountedComplex
  abiScratchEffect abiScratchFootprint abiDecoderAllocation abiDecoderFrame
  abiDecoderFrameCompose abiDecoderFootprint abiDecoderProtectedScratch abiDecoderContract abiDecoderLoop
  abiEncoderArrayParent compileEnv valueEncoding venomState words arithmetic
  finite_map fragGasPath bodyIntCallEncoderCountedPrefix abiScratchInput
  abiScratchOwnedPrefix abiScratchPrefix abiEncoderComplexPrefix abiEncoderMembersDefs
  abiScratchArrayEntry abiScratchLeafEffect abiEncoderArrayPrefix abiEncoderArrayHeaderMemory
  abiDecoderArrayHeader abiDecoderReentry abiEncoderInputFrame abiDecoderGuards venomInst
  abiScratchEncoderContract abiDecoderArrayLoopInit abiScratchCursor
  abiScratchPhaseCompose abiEncoderArrayContext abiEncoderArrayBodyCode
  bodyIntCallDecoderCountedPrimitive entrySinkExtraction rich_list instIdxIndep fragExec
  list emitHelperProps abiDecoderDynamicLoopSetup abiEncoderArrayRound
  bodyIntCallDecoderCountedControl abiDecoderArrayBackedge abiScratchArrayPrepare
  abiScratchAddress abiEncoderInput contractABI abiScratchStatic
  abiScratchMemberContract abiEncoderMemberSpine abiEncoderStatic abiEncoderLeafCode
  bodyIntCallEncoderCountedSpine abiScratchAfterAddress abiEncoderAdmissible
  abiScratchFrameCompose abiEncoderArrayFrame pred_set abiEncoderArrayDynamicMemory valueEncodingProps
  abiScratchArraySpine abiEncoderArrayTail abiEncoderMemberPhaseRaw abiScratchMemberAdapter
  abiEncoderCounters abiScratchArrayTail abiScratchChild abiEncoderResultLive

Theorem intcall_scratch_array_parent_finish:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  mem_bytes_at d len initial.vs_memory = bytes /\ len <= output_size /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. mem_bytes_at d len actual.vs_memory = bytes /\
    eval_operand out actual = SOME (n2w len) /\ mload slot actual = n2w len /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ _`
      (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> decide_tac) >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_scratch_registered_member >> simp[] >> qexists_tac `site` >> simp[]) >>
  qpat_assum `abi_footprint_disjoint d output_size _`
    (qspecl_then [`slot`, `32`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
  simp_tac bool_ss [] >> disch_tac >>
  drule_all intcall_encoder_array_finish_counted >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  gvs[WORD_ADD_0] >>
  `abi_decode_footprint_frame [(slot,32)] initial actual` by fs[abi_decode_frame_footprint] >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  drule_all abi_scratch_single_write >>
  disch_then (qspecl_then [`output_size`, `d`] assume_tac) >>
  `abi_footprint_disjoint d len [(slot,32)]` by (simp[abi_footprint_disjoint_def] >> decide_tac) >>
  drule_all abi_decode_footprint_frame_slice >> disch_tac >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexistsl_tac [`actual`, `n`] >> simp[]
QED

Theorem intcall_scratch_zero_cursor_prepare:
  abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (cursor_op,prepared) /\
  fn_has_code st prepared func /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ prepared.cs_next_id <= last /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot n. abi_scratch_input ei at av prepared src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_cursor T cursor_op st.cs_next_id slot first st.cs_next_id prepared 0 actual /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`] intcall_scratch_encoder_prefix_counted) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_scratch_owned_prefix_frame >> disch_tac >>
  drule_all abi_scratch_prefix_effect >>
  disch_then (qspecl_then [`output_size`, `d`] assume_tac) >>
  `st.cs_next_var <= st.cs_next_var` by simp[] >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
  `abi_scratch_input ei at av prepared src dst sb source_cap d output_size first last b cap actual` by
    (irule abi_scratch_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexistsl_tac [`actual`, `slot`, `n`] >> gvs[]
QED

Theorem intcall_scratch_array_count_prepare:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      st' src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_decoder_operand_live st'.cs_next_var cnt /\ eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encoder_array_count_live >> disch_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule_all intcall_encoder_array_count_counted >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_footprint_frame [(d,32)] initial actual` by fs[abi_decode_frame_footprint] >>
  drule_all abi_encoder_input_frame >> disch_tac >>
  `abi_encoder_array_prefix ty avs 0 d actual.vs_memory` by
    (irule abi_encoder_array_prefix_empty >> simp[]) >>
  `abi_decode_frame d output_size initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`d`, `32`] >> simp[]) >>
  `abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  `st.cs_next_var <= st.cs_next_var` by simp[] >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  `st.cs_next_var <= st'.cs_next_var` by decide_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st' src dst sb source_cap d output_size first last b cap actual` by
    (irule abi_scratch_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexistsl_tac [`actual`, `n`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_array_parent_prepare:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= hi /\ hi <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot n.
    abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      loop_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    abi_decoder_operand_live loop_st.cs_next_var (SND ops) /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_encode_array_prefix_context >> strip_tac >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ allocated.cs_next_id <= last /\
   loop_st.cs_next_id <= last /\ first <= allocated.cs_next_id /\ st.cs_next_id < last /\
   st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= loop_st.cs_next_var /\
   allocated.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  drule_all intcall_scratch_zero_cursor_prepare >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial allocated_state` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial allocated_state`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  drule_all intcall_scratch_array_count_prepare >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_scratch_input _ _ _ allocated _ _ _ _ _ _ _ _ _ _ allocated_state`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_scratch_cursor_protected >> disch_then drule >>
  impl_tac >- (asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >> disch_tac >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id loop_st 0 actual` by
    (irule abi_encoder_cursor_mono >> qexists_tac `allocated` >> asm_simp_tac bool_ss []) >>
  `abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial allocated_state` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `allocated.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap allocated_state actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `loop_st.cs_next_id`, `allocated.cs_next_id`, `allocated.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all abi_scratch_effect_trans >> disch_tac >>
  `?nsum. gas_path ctx func initial nsum (OK actual)` by metis_tac[gas_path_then] >>
  `abi_decode_sim ctx func initial actual` by
    (irule intcall_encoder_path_sim >> goal_assum (drule_at Any)) >>
  qexistsl_tac [`actual`, `slot`] >> simp[] >> metis_tac[]
QED

Theorem intcall_scratch_array_finish_protected:
  abi_encoder_cursor T parent_ptr parent_site parent_slot first parent_site loop_st 0 ready /\
  abi_scratch_effect first last loop_st.cs_next_id loop_end.cs_next_id loop_st.cs_next_var
    limit_st d output_size b cap ready encoded /\
  abi_decoder_budget first last b cap ready /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap ready) /\
  loop_st.cs_next_var <= loop_end.cs_next_var /\ loop_st.cs_next_id <= loop_end.cs_next_id /\
  parent_site < loop_st.cs_next_id /\ loop_end.cs_next_id <= last /\ parent_site < final.cs_next_id /\
  abi_encode_array_finish parent_ptr size_op loop_end = (out,final) /\ fn_has_code loop_end final func /\
  eval_operand size_op encoded = SOME (n2w len) /\ abi_decoder_operand_live loop_end.cs_next_var size_op /\
  mem_bytes_at d len encoded.vs_memory = bytes /\ len <= output_size /\
  final.cs_next_var <= limit_st.cs_next_var /\ ~encoded.vs_halted /\
  encoded.vs_current_bb = loop_end.cs_current_bb /\ encoded.vs_inst_idx = LENGTH loop_end.cs_current_insts ==>
  ?actual n. mem_bytes_at d len actual.vs_memory = bytes /\ eval_operand out actual = SOME (n2w len) /\
    abi_scratch_effect first last parent_site final.cs_next_id loop_end.cs_next_var
      limit_st d output_size b cap encoded actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual /\ gas_path ctx func encoded n (OK actual)
Proof
  strip_tac >>
  `first <= loop_st.cs_next_id /\ parent_site < last` by
    (fs[abi_encoder_cursor_def] >> decide_tac) >>
  drule abi_scratch_cursor_protected >> disch_then drule >>
  impl_tac >- (asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >> disch_tac >>
  `abi_encoder_cursor T parent_ptr parent_site parent_slot first parent_site loop_end 0 encoded` by
    (irule abi_encoder_cursor_mono >> qexists_tac `loop_st` >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_cursor T _ _ _ _ _ loop_end _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ ready encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap encoded)` by
    (irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `ready` >> simp[]) >>
  drule_all (Q.INST [`lo` |-> `parent_site:num`, `hi` |-> `final.cs_next_id`]
    intcall_scratch_array_parent_finish) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> simp[] >> metis_tac[]
QED

Theorem intcall_encoder_array_addresses_counted:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') /\ fn_has_code st st' func /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. eval_operand (FST (FST coords)) actual = SOME (n2w j) /\
    eval_operand (SND (FST coords)) actual = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) actual = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) actual = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule abi_encode_array_addresses_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_encode_array_addresses_sequence >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  goal_assum (drule_at Any) >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> metis_tac[]
QED

Theorem intcall_encoder_array_backedge_counted:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s) /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] s actual /\ gas_path ctx func s 0 (OK actual)
Proof
  strip_tac >> drule_all abi_encoder_array_backedge_execute >>
  disch_then (qspecl_then [`0`, `ctx`] strip_assume_tac) >>
  `ip <> Var (STRING #"%" (toString next))` by
    (irule abi_decoder_live_excludes_output >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all intcall_decode_backedge_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `actual` >> gvs[w2n_n2w]
QED

Theorem intcall_scratch_array_prepare:
  abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n.
    abi_scratch_input ei ty (EL j avs) prepared (SND (FST coords)) (FST (SND coords))
      (sb+32+j*msz) msz (d+32) (output_size-32) first last b cap actual /\
    abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    asz = abi_member_head_size ty /\ active = is_dynamic ty /\
    eval_operand (FST (FST coords)) actual = SOME (n2w j) /\
    eval_operand (SND (SND coords)) actual = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  drule_all intcall_encoder_array_addresses_counted >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_encoder_array_selected_input >> strip_tac >>
  `has_type (Array NONE ty) (ListV avs)` by metis_tac[abi_encoder_input_typed] >>
  drule_all abi_scratch_array_child_capacity >> strip_tac >>
  `actual.vs_memory = initial.vs_memory` by fs[abi_decoder_address_frame_def] >>
  drule_all abi_scratch_address >>
  disch_then (qspecl_then [`abi_decoder_ids first last`,
    `abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`] strip_assume_tac) >>
  `sb <= sb+32+j*msz /\ sb+32+j*msz+msz <= sb+source_cap /\
   d <= d+32 /\ d+32+(output_size-32) <= d+output_size` by decide_tac >>
  `abi_encoder_input ei ty (EL j avs) (sb+32+j*msz) msz actual.vs_memory` by gvs[] >>
  `abi_scratch_input ei ty (EL j avs) prepared (SND (FST coords)) (FST (SND coords))
      (sb+32+j*msz) msz (d+32) (output_size-32) first last b cap actual` by
    (drule abi_scratch_input_regions >>
     disch_then irule >> simp[]) >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexistsl_tac [`actual`, `n`] >> gvs[]
QED

(* A restricted recursive callback supplies semantics and counting together. *)
Theorem intcall_scratch_static_info:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  compile_abi_encode_static_info head src ei st = (out,end_st) /\ fn_has_code st end_st func /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\ offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+offset) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame
      ((d+offset,LENGTH (enc at av))::abi_decoder_child_scratch
        (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    intcall_encoder_core_path ctx func (ei,head,src,st,end_st,out) initial actual
Proof
  strip_tac >> drule abi_scratch_static_leaf >> disch_tac >>
  drule abi_encode_static_info_agrees >> disch_then (fn th =>
    qpat_assum `compile_abi_encode_static_info _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  drule_all abi_scratch_input_offset >> disch_tac >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  `abi_encoder_spine_core_code func (ei,head,src,st,end_st,out)` by
    simp[abi_encoder_spine_core_code_def] >>
  `abi_scratch_member_core_pre (at,av,sb,source_cap,d+offset) (first,last,b,cap,limit_st)
      (ei,head,src,st,end_st,out) initial` by simp[abi_scratch_member_core_pre_def] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qpat_x_assum `abi_scratch_member_core_post _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_member_core_post_def]) >>
  `abi_decode_footprint_frame
    ((d+offset,LENGTH (enc at av))::abi_decoder_child_scratch
      (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial) initial u` by
    fs[abi_scratch_effect_def] >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial u` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `u` >> simp[]
QED

Theorem intcall_scratch_array_static_body:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\ fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. mem_bytes_at (d+32+j*asz) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    eval_operand out actual = SOME (n2w j) /\
    abi_decode_footprint_frame
      ((d+32+j*asz,LENGTH (enc ty (EL j avs)))::
        abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_encode_array_static_body_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id /\
   st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  `LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size` by
    fs[abi_scratch_input_def] >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  `j*asz+LENGTH (enc ty (EL j avs)) <= output_size-32` by
    (gvs[Excl "enc_def"] >> decide_tac) >>
  drule_all intcall_scratch_array_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n (OK ready)` >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  drule_all (Q.INST [`offset` |-> `j*asz`, `d` |-> `d+32`] intcall_scratch_static_info) >>
  strip_tac >> rename1 `intcall_encoder_core_path ctx func _ ready actual` >>
  `eval_operand (FST (FST coords)) actual = SOME (n2w j)` by
    (irule abi_scratch_effect_operand >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_decode_footprint_frame
    ([(d+32+j*asz,LENGTH (enc ty (EL j avs)))] ++
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap ready) ready actual` by
    (irule abi_scratch_frame_subset_append >> conj_tac >- simp[] >>
     qexists_tac `abi_decoder_ids prepared.cs_next_id end_st.cs_next_id` >>
     conj_tac >- (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
     qpat_x_assum `abi_decode_footprint_frame (_::_) ready actual` mp_tac >>
     simp[Excl "enc_def"]) >>
  drule_all abi_scratch_frame_after_address >> disch_tac >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual` by
    (drule abi_scratch_effect_after_address >> disch_then irule >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qpat_assum `intcall_encoder_core_path _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [intcall_encoder_core_path_def]) >>
  `?k. gas_path ctx func initial k (OK actual)` by metis_tac[gas_path_then] >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `abi_decode_footprint_frame (_ ++ _) initial actual` mp_tac >>
  simp[Excl "enc_def"]
QED

Theorem intcall_scratch_array_static_body_memory:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\ fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st j actual /\ eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  `owner_st.cs_next_id <= last /\ first <= st.cs_next_id /\ site < last /\ site < st.cs_next_id` by decide_tac >>
  drule_all abi_encoder_cursor_bounds >> strip_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial` by
    (irule abi_scratch_input_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `mload (w2n (n2w slot:bytes32)) initial = n2w j` by simp[w2n_n2w] >>
  drule_all intcall_scratch_array_static_body >> strip_tac >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ owner_st _ _ _ _ _ _ _ _ _ _ initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory` by
    (gvs[Excl "enc_def"] >> irule abi_scratch_array_static_step >>
     simp[Excl "enc_def"] >>
     qexistsl_tac [`abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`,
       `initial`, `output_size`] >> simp[Excl "enc_def"]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_cursor T ip site slot first lo owner_st j actual` by
    (irule abi_scratch_cursor_protected >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `owner_st.cs_next_var <= owner_st.cs_next_var` by simp[] >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  qexistsl_tac [`actual`, `n`] >> simp[]
QED

Theorem intcall_scratch_array_backedge:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\ eval_operand ip initial = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
  ?actual. mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op initial) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
    gas_path ctx func initial 0 (OK actual)
Proof
  strip_tac >> drule_all intcall_encoder_array_backedge_counted >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  `abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual` by
    (irule abi_scratch_single_write >> simp[] >> qexistsl_tac [`site`, `slot`] >> simp[]) >>
  qexists_tac `actual` >> simp[]
QED

Theorem intcall_scratch_array_backedge_memory:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs k d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  owner_st.cs_next_var <= next /\ owner_st.cs_next_id <= last /\
  abi_decoder_budget first last b cap initial ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs k d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_scratch_effect first last site (site+1) next limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    gas_path ctx func initial 0 (OK actual)
Proof
  strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `site < last /\ site+1 <= last /\ site <= site /\ site < site+1` by decide_tac >>
  drule_all abi_encoder_cursor_bounds >> strip_tac >>
  `abi_decoder_operand_live next ip` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all (Q.INST [`lo` |-> `site:num`, `hi` |-> `site+1`]
    intcall_scratch_array_backedge) >>
  disch_then (qspecl_then [`output_size`, `d`, `ctx`] strip_assume_tac) >>
  `abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(slot,32)]` >> simp[] >>
     qexistsl_tac [`slot`, `32`] >> simp[] >>
     irule abi_scratch_registered_member >> simp[] >> qexists_tac `site` >> simp[abi_decoder_ids_def]) >>
  drule abi_encoder_input_typed >> disch_tac >>
  drule_all abi_encoder_array_prefix_output_frame >> disch_tac >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  `FLOOKUP actual.vs_allocas site = SOME (slot,32)` by simp[] >>
  `abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual` by
    (drule_all abi_scratch_cursor_registered >> simp[]) >>
  qexists_tac `actual` >> simp[]
QED

Theorem intcall_scratch_array_static_round:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\ lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = end_st.cs_current_insts ++ abi_decode_backedge_insts end_st.cs_next_id
    (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString end_st.cs_next_var)) ip hdr /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id+3 <= last /\
  end_st.cs_next_var+1 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_encode_array_static_body_context >> strip_tac >>
  drule abi_encode_array_static_body_index >> disch_tac >>
  `owner_st.cs_next_id <= last /\ end_st.cs_next_id <= last /\
   end_st.cs_next_var <= limit_st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var /\
   owner_st.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  drule_all intcall_scratch_array_static_body_memory >> strip_tac >>
  rename1 `gas_path ctx func initial n (OK encoded)` >>
  qpat_assum `out = Var _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `lookup_block encoded.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `j <= LENGTH avs` by decide_tac >>
  drule_all abi_encoder_array_prefix_types >> strip_tac >>
  drule_all (Q.INST [`n` |-> `LENGTH (avs:abi_value list)`]
    intcall_scratch_array_backedge_memory) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `first <= site /\ site <= st.cs_next_id` by (fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial encoded` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >>
     simp[] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `site+1`, `site`, `end_st.cs_next_var`, `output_size`] >>
     simp[] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> simp[] >> qexists_tac `encoded` >> simp[]) >>
  `gas_path ctx func initial n (OK actual)` by
    (drule_all gas_path_then >> simp[]) >>
  qexistsl_tac [`actual`, `n`] >> simp[]
QED

Theorem intcall_encoder_array_tail_raw_path:
  abi_encode_array_tail data_op dyn_ptr st = (ops,final) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?n. gas_path ctx func initial n (OK ready)
Proof
  strip_tac >> drule abi_encode_array_tail_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts final.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all intcall_encoder_phase_raw_path >> simp[]
QED

Theorem intcall_scratch_array_tail_prepare:
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\ abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_scratch_input ei at av prepared src (SND ops) sb source_cap (d+off)
      (LENGTH (enc at av)) first last b cap actual /\
    eval_operand (FST ops) actual = SOME (n2w off) /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    abi_decoder_operand_live prepared.cs_next_var (FST ops) /\
    abi_decoder_operand_live prepared.cs_next_var (SND ops) /\
    abi_decoder_operand_live prepared.cs_next_var dyn_ptr /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_member_phase_raw st prepared initial actual /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `eval_operand data_op initial = SOME (n2w d) /\ abi_decoder_operand_live st.cs_next_var data_op` by
    fs[abi_scratch_input_def] >>
  drule_all abi_encoder_member_tail_raw >> strip_tac >>
  drule_all abi_scratch_array_prepare_raw_transport >> strip_tac >>
  drule_all intcall_encoder_array_tail_raw_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_array_tail_finish:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,final) /\ fn_has_code st final func /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  mem_bytes_at (d+off) len initial.vs_memory = bytes /\
  d <= h /\ h+32 <= d+off /\ off+len <= output_size /\ d+output_size < dimword (:256) /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ site IN abi_decoder_ids first last /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. mem_bytes_at (d+off) len actual.vs_memory = bytes /\
    mem_word_at h actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+len) /\
    eval_operand out actual = SOME (n2w len) /\ FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_encoder_child_suffix_post out st limit_st h slot off len initial actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by
    (drule abiDecoderIndexInitTheory.abi_decoder_budget_word_bound >> simp[]) >>
  `h < dimword (:256) /\ slot < dimword (:256)` by decide_tac >>
  `abi_encoder_spine_cursor_input (head,dyn_ptr,offset,child_len,st,final,limit_st) initial` by
    (simp[abi_encoder_spine_cursor_input_def] >>
     qexistsl_tac [`h`, `slot`, `off`, `len`] >> simp[]) >>
  drule_all abi_encoder_spine_cursor_run >> strip_tac >>
  drule_all abi_scratch_dynamic_finish_raw_transport >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all intcall_encoder_suffix_raw_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_array_tail_child:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_spine_core_code func (ei,SND ops,src,prepared,child_end,child_len) /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  eval_operand head initial = SOME (n2w h) /\ abi_decoder_operand_live st.cs_next_var head /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\ abi_decoder_budget first last b cap initial /\
  first <= site /\ site < st.cs_next_id /\ first <= prepared.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ child_end.cs_next_id <= last /\
  child_end.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready encoded n.
    abi_decoder_address_frame st.cs_next_var initial ready /\
    abi_scratch_member_core_pre (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
      (ei,SND ops,src,prepared,child_end,child_len) ready /\
    abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
      (ei,SND ops,src,prepared,child_end,child_len) ready encoded /\
    eval_operand head encoded = SOME (n2w h) /\ eval_operand dyn_ptr encoded = SOME (n2w slot) /\
    eval_operand (FST ops) encoded = SOME (n2w off) /\
    FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\ mload slot encoded = n2w off /\
    fresh_vars_wrt limit_st encoded /\ abi_decoder_budget first last b cap encoded /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial encoded /\
    gas_path ctx func initial n (OK encoded)
Proof
  strip_tac >> drule abi_encode_array_tail_shape >> strip_tac >>
  qpat_assum `abi_encoder_spine_core_code _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_core_code_def]) >>
  drule abi_encoder_counters >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ site < prepared.cs_next_id /\ site < last` by decide_tac >>
  drule_all intcall_scratch_array_tail_prepare >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n (OK ready)` >>
  `eval_operand head ready = SOME (n2w h) /\ FLOOKUP ready.vs_allocas site = SOME (slot,32) /\
   mload slot ready = n2w off` by
    (fs[abi_decoder_address_frame_def, mload_def] >> metis_tac[]) >>
  `abi_scratch_member_core_pre (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
      (ei,SND ops,src,prepared,child_end,child_len) ready` by simp[abi_scratch_member_core_pre_def] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `abi_decoder_operand_live prepared.cs_next_var head` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all abi_scratch_member_core_saved >> strip_tac >>
  `eval_operand head u = SOME (n2w h) /\ eval_operand dyn_ptr u = SOME (n2w slot) /\
   eval_operand (FST ops) u = SOME (n2w off)` by metis_tac[] >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap ready u` by
    fs[abi_scratch_member_core_post_def, abi_scratch_effect_def] >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial u` by
    (drule_all abi_scratch_evolution_trans >> simp[]) >>
  qpat_assum `intcall_encoder_core_path _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [intcall_encoder_core_path_def]) >>
  `?k. gas_path ctx func initial k (OK u)` by metis_tac[gas_path_then] >>
  qexistsl_tac [`ready`, `u`] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_array_dynamic_tail:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND ops) src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
  fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\ eval_operand head initial = SOME (n2w (d+ho)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_word_at (d+ho) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    eval_operand child_len actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_input ei at av sb source_cap actual.vs_memory /\
    abi_decode_footprint_frame
      ([(d+ho,32);(d+off,LENGTH (enc at av))] ++
        abi_decoder_child_scratch (abi_decoder_ids lo end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_scratch_array_tail_code >> strip_tac >>
  `abi_encoder_spine_core_code func (ei,SND ops,src,prepared,child_end,child_len)` by
    simp[abi_encoder_spine_core_code_def] >>
  `first <= site /\ site < last` by (fs[abi_decoder_ids_def] >> decide_tac) >>
  drule_all (Q.INST [`head` |-> `head:operand`, `h` |-> `d+ho`] intcall_scratch_array_tail_child) >>
  strip_tac >>
  rename1 `gas_path ctx func initial n (OK encoded)` >>
  qpat_assum `abi_scratch_member_core_post _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_member_core_post_def]) >>
  `d+output_size < dimword (:256) /\
   abi_footprint_disjoint d output_size
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_scratch_input_def] >>
  `abi_footprint_disjoint d output_size
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap encoded)` by
    (irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  `d <= d+ho /\ d+ho+32 <= d+off` by decide_tac >>
  drule_all intcall_scratch_array_tail_finish >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `lo <= prepared.cs_next_id /\ child_end.cs_next_id <= end_st.cs_next_id /\
   st.cs_next_var <= prepared.cs_next_var /\ site IN abi_decoder_ids lo end_st.cs_next_id /\
   d <= d+off /\ d+off+LENGTH (enc at av) <= d+output_size /\ d+ho+32 <= d+output_size` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_scratch_child_effect >> strip_tac >>
  `abi_encoder_input ei at av sb source_cap actual.vs_memory` by
    (drule_all abi_scratch_effect_source >> simp[]) >>
  `?k. gas_path ctx func initial k (OK actual)` by metis_tac[gas_path_then] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_array_dynamic_body:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\ fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. mem_bytes_at (d+32+off) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    mem_word_at (d+32+j*asz) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ eval_operand out actual = SOME (n2w j) /\
    abi_decode_footprint_frame
      ([(d+32+j*asz,32);(d+32+off,LENGTH (enc ty (EL j avs)))] ++
        abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_scratch_effect first last site end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  `addressed.cs_next_var <= limit_st.cs_next_var /\ site < addressed.cs_next_id /\
   st.cs_next_var <= addressed.cs_next_var` by decide_tac >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  `LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size` by fs[abi_scratch_input_def] >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  `j*asz+32 <= off /\ off+LENGTH (enc ty (EL j avs)) <= output_size-32` by
    (gvs[Excl "enc_def"] >> decide_tac) >>
  drule_all intcall_scratch_array_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n (OK ready)` >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  `abi_decoder_operand_live addressed.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dyn_ptr ready = SOME (n2w slot) /\ mload slot ready = n2w off /\
   FLOOKUP ready.vs_allocas site = SOME (slot,32)` by fs[abi_decoder_address_frame_def, mload_def] >>
  `site <= site` by simp[] >>
  drule_all (Q.INST [`ho` |-> `j*asz`, `d` |-> `d+32`, `lo` |-> `site:num`]
    intcall_scratch_array_dynamic_tail) >> strip_tac >>
  rename1 `gas_path ctx func ready n' (OK actual)` >>
  `eval_operand (FST (FST coords)) actual = SOME (n2w j)` by
    (irule abi_scratch_effect_operand >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_decode_footprint_frame
    ([(d+32+j*asz,32);(d+32+off,LENGTH (enc ty (EL j avs)))] ++
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap ready) ready actual` by
    (irule abi_scratch_frame_subset_append >> conj_tac >- simp[] >>
     qexists_tac `abi_decoder_ids site end_st.cs_next_id` >>
     conj_tac >- (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >> simp[]) >>
  drule_all abi_scratch_frame_after_address >> disch_tac >>
  `abi_scratch_effect first last site end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (drule abi_scratch_effect_after_address >> disch_then irule >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `?k. gas_path ctx func initial k (OK actual)` by metis_tac[gas_path_then] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_array_dynamic_iteration:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\ fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      st src dst sb source_cap d output_size first last b cap actual /\
    mload slot actual = n2w (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all intcall_scratch_array_dynamic_body >> strip_tac >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory` by
    (gvs[Excl "enc_def"] >> irule abi_scratch_array_dynamic_step >>
     simp[Excl "enc_def"] >>
     qexistsl_tac [`abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`,
       `initial`, `output_size`] >> simp[Excl "enc_def"]) >>
  `st.cs_next_var <= st.cs_next_var` by simp[] >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  `is_dynamic ty` by fs[] >>
  drule_all abi_encoder_array_tail_sum_suc >> disch_tac >>
  qexistsl_tac [`actual`, `n`] >> asm_simp_tac bool_ss [GSYM mem_word_at_eq_mload, ADD_ASSOC]
QED

Theorem intcall_scratch_array_dynamic_body_memory:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\ fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip index_site index_slot first lo owner_st j initial /\
  abi_encoder_cursor T dyn_ptr site slot first lo owner_st off initial /\ index_site < site /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  j < LENGTH avs /\ owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip index_site index_slot first lo owner_st j actual /\
    abi_encoder_cursor T dyn_ptr site slot first lo owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_encoder_cursor T dyn_ptr _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  `site < st.cs_next_id /\ index_site < last /\ site < last /\ owner_st.cs_next_id <= last` by decide_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (mp_then Any mp_tac abi_encoder_cursor_bounds) >>
  disch_then drule_all >> strip_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial` by
    (irule abi_scratch_input_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_decoder_operand_live st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  `mload (w2n (n2w index_slot:bytes32)) initial = n2w j` by simp[w2n_n2w] >>
  drule_all intcall_scratch_array_dynamic_iteration >> strip_tac >>
  `abi_scratch_effect first last site end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `abi_scratch_input _ _ _ owner_st _ _ _ _ _ _ _ _ _ _ initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `abi_encoder_cursor T ip index_site index_slot first lo owner_st j actual` by
    (irule abi_scratch_cursor_protected >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_cursor T dyn_ptr site slot first lo owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual` by
    (drule_all abi_scratch_cursor_registered >> simp[]) >>
  `owner_st.cs_next_var <= owner_st.cs_next_var` by simp[] >>
  drule_all abi_scratch_input_effect >> disch_tac >>
  qexistsl_tac [`actual`, `n`] >> simp[]
QED

Theorem intcall_scratch_array_backedge_cursor:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs k d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  abi_encoder_cursor T cursor_op cursor_site cursor_slot first lo owner_st off initial /\
  site < cursor_site /\ owner_st.cs_next_var <= next /\ owner_st.cs_next_id <= last /\
  abi_decoder_budget first last b cap initial ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs k d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_encoder_cursor T cursor_op cursor_site cursor_slot first lo owner_st off actual /\
    abi_scratch_effect first last site (site+1) next limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    gas_path ctx func initial 0 (OK actual)
Proof
  strip_tac >> drule_all intcall_scratch_array_backedge_memory >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `first <= site /\ site+1 <= last /\ cursor_site < last` by
    (fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by fs[abi_scratch_input_def] >>
  `abi_encoder_cursor T cursor_op cursor_site cursor_slot first lo owner_st off actual` by
    (qpat_assum `abi_encoder_cursor T cursor_op _ _ _ _ _ _ initial`
       (mp_then Any mp_tac abi_scratch_cursor_protected) >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`limit_st`, `next`, `site+1`, `site`] >> simp[] >> decide_tac) >>
  qexists_tac `actual` >> simp[]
QED

Theorem intcall_scratch_array_dynamic_round:
  (!value resources cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  P ei /\ abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\ fn_has_code st end_st func /\
  lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = end_st.cs_current_insts ++ abi_decode_backedge_insts end_st.cs_next_id
    (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString end_st.cs_next_var)) ip hdr /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first lo owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  site < cursor_site /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id+3 <= last /\
  end_st.cs_next_var+1 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first lo owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  drule abi_encode_array_dynamic_body_index >> disch_tac >>
  `owner_st.cs_next_id <= last /\ end_st.cs_next_id <= last /\
   end_st.cs_next_var <= limit_st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var /\
   owner_st.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  `LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) =
   LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))` by simp[] >>
  drule_all intcall_scratch_array_dynamic_body_memory >> strip_tac >>
  rename1 `gas_path ctx func initial n (OK encoded)` >>
  qpat_assum `out = Var _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `lookup_block encoded.vs_current_bb func.fn_blocks = SOME bb` by
    (qpat_x_assum `lookup_block end_st.cs_current_bb _ = _` mp_tac >> simp[]) >>
  `j <= LENGTH avs` by decide_tac >>
  drule_all abi_encoder_array_prefix_types >> strip_tac >>
  drule_all (Q.INST [`n` |-> `LENGTH (avs:abi_value list)`]
    intcall_scratch_array_backedge_cursor) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `first <= site /\ site <= cursor_site /\ site <= st.cs_next_id` by
    (fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial encoded` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `cursor_site`, `owner_st.cs_next_var`, `output_size`] >>
     simp[] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `site+1`, `site`, `end_st.cs_next_var`, `output_size`] >>
     qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ encoded actual` mp_tac >>
     simp[Excl "enc_def"] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> simp[] >> qexists_tac `encoded` >> simp[]) >>
  `?k. gas_path ctx func initial k (OK actual)` by metis_tac[gas_path_then] >>
  goal_assum (drule_at Any) >> simp[]
QED
