Theory abiEncoderArrayParent
Ancestors
  abiEncoderArrayFinish abiEncoderChildEffect abiDecoderEffect abiDecoderAllocation
  abiDecoderProtectedScratch abiDecoderArrayInitExec abiDecoderPrimitiveLoopFrames
  abiDecoderFrameCompose abiDecoderFrame abiDecoderContract abiDecoderReentry abiDecoderLoop
  fragExec compileEnv venomState finite_map words list arithmetic pred_set
  abiEncoderArrayInitCode abiEncoderArrayScalarCode abiEncoderArrayCount
  abiEncoderZeroCursorPrepare abiEncoderComplexPrefix abiEncoderArrayCursor
  abiEncoderMembersDefs abiEncoderArrayMemory abiDecoderArrayLoopInit abiDecoderGuards
  emitHelperProps valueEncoding contractABI rich_list

(* ===== Finish ===== *)

(* Updating the registered parent cursor preserves the completed ABI output and other scratch. *)

Theorem abi_encoder_array_parent_finish:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  mem_bytes_at d len initial.vs_memory = bytes /\ len <= output_size /\
  (d+output_size <= b \/ b+cap <= d) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\
    eval_operand out actual = SOME (n2w len) /\ mload slot actual = n2w len /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  `slot < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`old_word` |-> `0w:bytes32`, `size_word` |-> `n2w len:bytes32`]
    abi_encode_array_finish_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial actual /\
   abi_decode_footprint_frame [(d,output_size);(slot,32)] initial actual` by
    (conj_tac >> irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  `abi_decoder_scratch_frame first last lo hi initial actual` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
      `sz` |-> `output_size:num`] abi_encoder_owned_scratch_frame) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame b cap initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`slot`, `32`] >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,output_size);(b,cap)] initial actual` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`b`, `cap`] >> simp[]) >>
  `mem_bytes_at d len actual.vs_memory = bytes` by
    (qpat_assum `abi_decode_frame slot 32 initial actual`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     `d+len <= slot \/ slot+32 <= d` by decide_tac >>
     qpat_x_assum `!p n. _` (qspecl_then [`d`, `len`] mp_tac) >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_decoder_effect_def]
QED

(* ===== Prepare ===== *)

(* Execute the actual parent allocation and count copy before either array loop. *)

Theorem abi_encode_array_prefix_context:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func ==>
  ?parent_ptr allocated cnt.
    abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (parent_ptr,allocated) /\
    abi_decode_array_header dst src MLOAD allocated = (cnt,loop_st) /\ ops = (parent_ptr,cnt) /\
    fn_has_code st allocated func /\ fn_has_code allocated loop_st func /\
    allocated.cs_next_var = st.cs_next_var+1 /\ allocated.cs_next_id = st.cs_next_id+2 /\
    loop_st.cs_next_var = st.cs_next_var+2 /\ loop_st.cs_next_id = st.cs_next_id+4
Proof
  strip_tac >> drule abi_encode_array_prefix_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `st` |-> `allocated`, `st'` |-> `loop_st`]
    abi_decode_array_header_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  `cs_extends st allocated /\ cs_extends allocated loop_st` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  mp_tac (Q.SPECL [`st`, `allocated`, `loop_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM abi_decode_index_init_complex_prefix]) >>
  pure_rewrite_tac [GSYM abi_decode_index_init_complex_prefix] >>
  qexistsl_tac [`parent_ptr`, `allocated`, `cnt`] >> asm_simp_tac arith_ss []
QED

Theorem abi_encoder_array_parent_prepare:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= hi /\ hi <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_array_memory ei asz msz active ty avs loop_st src dst sb source_cap d output_size b cap 0 actual /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    abi_decoder_operand_live loop_st.cs_next_var (SND ops) /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_prefix_context >> strip_tac >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ allocated.cs_next_id <= hi /\
   st.cs_next_id < last /\ st.cs_next_id < allocated.cs_next_id /\
   st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= loop_st.cs_next_var /\
   allocated.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `cursor_op` |-> `parent_ptr`, `prepared` |-> `allocated`]
    abi_encoder_zero_cursor_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial allocated_state` >>
  `fresh_vars_wrt limit_st allocated_state /\ abi_decoder_budget first last b cap allocated_state` by
    fs[abi_decoder_effect_def] >>
  mp_tac (Q.INST [`st` |-> `allocated`, `st'` |-> `loop_st`,
    `initial` |-> `allocated_state:venom_state`, `lo` |-> `allocated.cs_next_id`]
    abi_encoder_array_count_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id allocated 0 actual` by
    (mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `parent_ptr`, `site` |-> `st.cs_next_id`,
      `lo` |-> `st.cs_next_id`, `st` |-> `allocated`, `off` |-> `0:num`,
      `owned_lo` |-> `allocated.cs_next_id`, `owned_hi` |-> `hi:num`, `next` |-> `allocated.cs_next_var`,
      `initial` |-> `allocated_state:venom_state`, `sz` |-> `output_size:num`]
      abi_encoder_cursor_effect_protected) >> impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]) >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id loop_st 0 actual` by
    (drule_all abi_encoder_cursor_mono >> asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap allocated_state actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `hi`, `allocated.cs_next_id`, `allocated.cs_next_var`, `output_size`] >>
     asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `allocated_state` >> asm_simp_tac bool_ss []) >>
  qpat_assum `loop_st.cs_next_var = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qexistsl_tac [`actual`, `slot`] >> asm_simp_tac (srw_ss()) [Excl "enc_def"] >>
  irule abi_decode_sim_trans >> qexists_tac `allocated_state` >> asm_simp_tac bool_ss []
QED
