Theory abiScratchArrayRun
Ancestors
  abiScratchArrayStaticLoop abiScratchArrayDynamicLoop abiScratchEncoderContract abiDecoderLoop
  abiDecoderReentry abiDecoderContract compileEnv valueEncoding contractABI venomState words
  list arithmetic abiScratchEffect abiScratchFootprint abiEncoderArrayParent
  abiDecoderAllocation abiDecoderProtectedScratch abiDecoderFrameCompose abiDecoderFrame
  finite_map abiScratchZeroCursor abiScratchArrayEntry abiScratchCursor
  abiEncoderArrayHeaderMemory abiEncoderMembersDefs abiDecoderFootprint abiScratchPhaseCompose
  abiEncoderArrayContext

(* Select the actual proved static or dynamic array loop with precise resources.
   TOP-LEVEL: abi_scratch_array_selected_loop exposes a common executable
   interface for the complete parent array constructor. *)
Theorem abi_scratch_array_selected_loop:
  (if active then abi_scratch_encoder ei else abi_encoder_static_leaf ei) /\
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final)
    else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final)) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `active` >> simp_tac bool_ss [COND_CLAUSES] >> strip_tac >>
  FIRST [drule_all abi_scratch_array_dynamic_loop, drule_all abi_scratch_array_static_loop] >>
  disch_then (qspec_then `ctx` assume_tac) >> asm_simp_tac bool_ss []
QED

(* ===== Finish ===== *)

(* Update the real registered parent cursor after encoding the array payload.
   TOP-LEVEL: abi_scratch_array_parent_finish preserves all encoded bytes
   using the cursor's physical slot and returns an owned recursive effect. *)

Theorem abi_scratch_array_parent_finish:
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
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\
    eval_operand out actual = SOME (n2w len) /\ mload slot actual = n2w len /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ _`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> decide_tac) >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_scratch_registered_member >> simp[] >> qexists_tac `site` >> simp[]) >>
  qpat_assum `abi_footprint_disjoint d output_size _`
    (qspecl_then [`slot`, `32`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
  asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  mp_tac (Q.INST [`old_word` |-> `0w:bytes32`, `size_word` |-> `n2w len:bytes32`]
    abi_encode_array_finish_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial actual` by fs[abi_decode_frame_footprint] >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `sz` |-> `output_size:num`]
    abi_scratch_single_write) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `abi_footprint_disjoint d len [(slot,32)]` by (simp[abi_footprint_disjoint_def] >> decide_tac) >>
  mp_tac (Q.INST [`p` |-> `d:num`, `n` |-> `len:num`, `fp` |-> `[(slot:num,32:num)]`,
    `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_decode_footprint_frame_slice) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> simp[]
QED

(* ===== Prepare ===== *)

(* Execute the actual parent allocation and count copy with precise resources.
   TOP-LEVEL: abi_scratch_array_parent_prepare establishes complete loop input,
   the zero parent cursor, the copied count and one composed owned effect. *)

Theorem abi_scratch_array_parent_prepare:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= hi /\ hi <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      loop_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    abi_decoder_operand_live loop_st.cs_next_var (SND ops) /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_prefix_context >> strip_tac >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ allocated.cs_next_id <= last /\
   loop_st.cs_next_id <= last /\ first <= allocated.cs_next_id /\ st.cs_next_id < last /\
   st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= loop_st.cs_next_var /\
   allocated.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `cursor_op` |-> `parent_ptr:operand`, `prepared` |-> `allocated`]
    abi_scratch_zero_cursor_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial allocated_state` >>
  rename1 `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id allocated 0 allocated_state` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial allocated_state`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  mp_tac (Q.INST [`st` |-> `allocated`, `st'` |-> `loop_st`, `initial` |-> `allocated_state:venom_state`]
    abi_scratch_array_count_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ allocated _ _ _ _ _ _ _ _ _ _ allocated_state`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `parent_ptr:operand`, `site` |-> `st.cs_next_id`,
    `lo` |-> `st.cs_next_id`, `st` |-> `allocated`, `off` |-> `0:num`, `sz` |-> `output_size:num`,
    `owned_lo` |-> `allocated.cs_next_id`, `owned_hi` |-> `loop_st.cs_next_id`, `next` |-> `allocated.cs_next_var`,
    `initial` |-> `allocated_state:venom_state`] abi_scratch_cursor_protected) >>
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
  `abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `allocated_state` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `slot`] >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `allocated_state` >> simp[]
QED

(* Finish through the parent cursor after the recursively executed array loop.
   TOP-LEVEL: abi_scratch_array_finish_protected derives preservation of the
   parent slot and completed output from the initial physical scratch footprint. *)
Theorem abi_scratch_array_finish_protected:
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
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\ eval_operand out actual = SOME (n2w len) /\
    abi_scratch_effect first last parent_site final.cs_next_id loop_end.cs_next_var
      limit_st d output_size b cap encoded actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `first <= loop_st.cs_next_id /\ parent_site < last` by
    (fs[abi_encoder_cursor_def] >> decide_tac) >>
  mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `parent_ptr:operand`, `site` |-> `parent_site:num`,
    `slot` |-> `parent_slot:num`, `lo` |-> `parent_site:num`, `st` |-> `loop_st`, `off` |-> `0:num`,
    `owned_lo` |-> `loop_st.cs_next_id`, `owned_hi` |-> `loop_end.cs_next_id`, `next` |-> `loop_st.cs_next_var`,
    `initial` |-> `ready:venom_state`, `actual` |-> `encoded:venom_state`, `sz` |-> `output_size:num`]
    abi_scratch_cursor_protected) >>
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
  mp_tac (Q.INST [`st` |-> `loop_end`, `initial` |-> `encoded:venom_state`,
    `site` |-> `parent_site:num`, `slot` |-> `parent_slot:num`, `lo` |-> `parent_site:num`,
    `hi` |-> `final.cs_next_id`] abi_scratch_array_parent_finish) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> gvs[]) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Execute the actual complete array encoder from buffer input.
   TOP-LEVEL: abi_scratch_array_run composes parent allocation/count copying,
   the selected real loop, protected parent completion and physical effects. *)
Theorem abi_scratch_array_run:
  (if active then abi_scratch_encoder ei else abi_encoder_static_leaf ei) /\
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) start = (out,final) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_context >> strip_tac >>
  `loop_st.cs_next_id <= last /\ loop_end.cs_next_id <= last /\
   loop_st.cs_next_var <= limit_st.cs_next_var /\ loop_end.cs_next_var <= limit_st.cs_next_var /\
   start.cs_next_id < loop_st.cs_next_id /\ start.cs_next_id < final.cs_next_id /\
   first <= loop_st.cs_next_id /\ start.cs_next_var <= loop_st.cs_next_var /\
   loop_end.cs_next_id <= final.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `hi` |-> `loop_st.cs_next_id`]
    abi_scratch_array_parent_prepare) >> impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  rename1 `abi_encoder_cursor T (FST ops) start.cs_next_id slot first start.cs_next_id loop_st 0 ready` >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`count_op` |-> `SND (ops:operand # operand)`, `start` |-> `loop_st`,
    `out` |-> `size_op`, `final` |-> `loop_end`, `initial` |-> `ready:venom_state`,
    `hi` |-> `loop_end.cs_next_id`] abi_scratch_array_selected_loop) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  qpat_assum `abi_scratch_input _ _ _ loop_st _ _ _ _ _ _ _ _ _ _ ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  mp_tac (Q.INST [`parent_ptr` |-> `FST (ops:operand # operand)`, `parent_site` |-> `start.cs_next_id`,
    `parent_slot` |-> `slot:num`, `len` |-> `LENGTH (enc (Array NONE ty) (ListV avs))`,
    `bytes` |-> `enc (Array NONE ty) (ListV avs)`] abi_scratch_array_finish_protected) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `prepared` |-> `loop_st`, `middle` |-> `loop_end`,
    `end_st` |-> `final`, `sz` |-> `output_size:num`] abi_scratch_phase_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  `abi_decode_sim ctx func initial encoded` by
    (irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED
