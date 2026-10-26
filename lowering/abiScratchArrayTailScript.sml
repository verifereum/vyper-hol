Theory abiScratchArrayTail
Ancestors
  abiScratchOwnedPrefix abiScratchSequence abiScratchPrefixReach abiScratchFootprint
  abiEncoderArrayTailInit abiEncoderSequence abiEncoderComplexPrefix abiEncoderMembersDefs
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderLoop
  compileEnv venomState venomInst finite_map pred_set words list arithmetic abiEncoderArrayTail
  abiEncoderChildCode abiEncoderArrayDynamicCode abiEncoderCounters abiEncoderResultLive
  abiDecoderProtectedScratch abiDecoderContract abiEncoderArrayFrame abiEncoderArrayPrefix
  abiEncoderInput abiEncoderInputFrame valueEncoding contractABI abiScratchChild
  abiScratchEncoderContract abiScratchAddress abiDecoderDynamicLoopSetup

(* ===== Scratch Array Tail ===== *)

(* Execute the computed array tail cursor with the precise scratch footprint.
   TOP-LEVEL: abi_scratch_array_tail_reach establishes real containing-function
   execution; its allocation and store preserve every earlier cursor. *)

Theorem abi_scratch_array_tail_sequence:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual
Proof
  strip_tac >> drule abi_encode_array_tail_init_shape >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  mp_tac (Q.INST [`count_op` |-> `count_op`, `asz` |-> `asz:num`, `cnt` |-> `cnt:num`,
    `dyn_ptr` |-> `dyn_ptr`, `st` |-> `st:compile_state`, `st'` |-> `st':compile_state`,
    `limit_st` |-> `limit_st:compile_state`, `first` |-> `first:num`, `last` |-> `last:num`,
    `b` |-> `b:num`, `cap` |-> `cap:num`, `initial` |-> `initial:venom_state`]
    abi_encode_array_tail_init_sequence) >> impl_tac >- gvs[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK actual` >>
  `actual.vs_alloca_next <= b+cap` by
    (fs[abi_encoder_complex_prefix_post_def, abi_decoder_budget_def] >> decide_tac) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (mp_tac (Q.SPECL [`emitted_insts st st'`, `initial`, `actual`,
       `abi_decoder_ids first last`, `b`, `cap`] abi_scratch_sequence_evolution) >> simp[]) >>
  `st.cs_next_id < st'.cs_next_id` by decide_tac >>
  drule_all abi_scratch_owned_prefix_frame >> disch_then assume_tac >>
  `abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual` by
    (qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
     mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `site` |-> `st.cs_next_id`,
       `slot` |-> `slot`, `sz` |-> `32`, `s` |-> `initial:venom_state`,
       `t` |-> `actual:venom_state`] abi_scratch_final_slot_frame) >> simp[]) >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_scratch_array_tail_reach:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr
      st.cs_next_var st.cs_next_id limit_st first last b cap initial actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual /\
    (!op site slot lo off. abi_encoder_cursor T op site slot first lo st off initial ==>
      abi_encoder_cursor T op site slot first lo st' off actual) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_scratch_array_tail_sequence >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK encoded` >>
  `~encoded.vs_halted` by fs[abi_encoder_complex_prefix_post_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qabbrev_tac `actual = encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  `abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr
    st.cs_next_var st.cs_next_id limit_st first last b cap initial actual /\
   abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
    initial actual` by simp[Abbr`actual`, abi_scratch_inst_idx] >>
  `st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id` by decide_tac >>
  `!op site slot lo off. abi_encoder_cursor T op site slot first lo st off initial ==>
    abi_encoder_cursor T op site slot first lo st' off actual` by
    (rpt gen_tac >> strip_tac >> drule_all abi_scratch_owned_prefix_parent >> simp[]) >>
  qexists_tac `actual` >> gvs[Abbr`actual`, abi_scratch_inst_idx]
QED

(* ===== Code ===== *)

(* Numeric and register resources for the three actual dynamic-child stages.
   TOP-LEVEL: abi_scratch_array_tail_code derives child limits, cursor bounds
   and the real child-exit phi condition from generated code and its budget. *)

Theorem abi_scratch_array_tail_code:
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND ops) src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
  fn_has_code child_end end_st func /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_operand_live st.cs_next_var head /\ abi_decoder_operand_live st.cs_next_var dyn_ptr ==>
  prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
  first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\
  lo <= prepared.cs_next_id /\ child_end.cs_next_id <= end_st.cs_next_id /\
  st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_var <= child_end.cs_next_var /\
  site < prepared.cs_next_id /\ site IN abi_decoder_ids first last /\
  site IN abi_decoder_ids lo end_st.cs_next_id /\ slot < dimword (:256) /\
  abi_decoder_operand_live prepared.cs_next_var head /\
  abi_decoder_operand_live child_end.cs_next_var dyn_ptr /\
  abi_decoder_operand_live child_end.cs_next_var child_len /\
  (prepared.cs_blocks = child_end.cs_blocks \/
    !bb. lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule abi_encode_result_live >> strip_tac >>
  drule_all abi_encode_array_dynamic_body_child_phi >> disch_tac >>
  `site IN abi_decoder_ids first last /\ site IN abi_decoder_ids lo end_st.cs_next_id` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by fs[abi_decoder_budget_def] >>
  `slot < dimword (:256)` by decide_tac >>
  `abi_decoder_operand_live prepared.cs_next_var head /\
   abi_decoder_operand_live child_end.cs_next_var dyn_ptr` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

(* ===== Input ===== *)

(* Computed tail initialization preserves complete array input and output data.
   TOP-LEVEL: abi_scratch_array_tail_input adds the actual tail cursor to the
   precise execution result, retaining every previously initialized cursor. *)

Theorem abi_scratch_array_tail_input:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual tail_slot.
    abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs j d actual.vs_memory /\
    abi_encoder_cursor T dyn_ptr st.cs_next_id tail_slot first st.cs_next_id st'
      (LENGTH avs*asz) actual /\
    (!op site slot lo off. abi_encoder_cursor T op site slot first lo st off initial ==>
      abi_encoder_cursor T op site slot first lo st' off actual) /\
    abi_encoder_complex_prefix_post [(AbiPrimWord,LENGTH avs*asz,0,F)] dyn_ptr
      st.cs_next_var st.cs_next_id limit_st first last b cap initial actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual /\
    abi_footprint_disjoint sb source_cap
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_scratch_array_tail_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `has_type (Array NONE ty) (ListV avs)` by
    (drule abi_encoder_input_typed >> simp[]) >>
  `abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap actual.vs_memory` by
    (drule_all abi_encoder_input_frame >> simp[]) >>
  `abi_encoder_array_prefix ty avs j d actual.vs_memory` by
    (drule_all abi_encoder_array_prefix_output_frame >> simp[]) >>
  `abi_decoder_operand_live st'.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  `abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`,
       `cap` |-> `cap:num`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
       `p` |-> `sb:num`, `n` |-> `source_cap:num`] abi_scratch_disjoint_advance) >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`,
       `cap` |-> `cap:num`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
       `p` |-> `d:num`, `n` |-> `output_size:num`] abi_scratch_disjoint_advance) >> simp[]) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  qexistsl_tac [`actual`, `slot`] >> gvs[abi_encoder_cursor_def] >> first_assum ACCEPT_TAC
QED

(* ===== Prepare ===== *)

(* Execute the actual cursor load and dynamic child destination calculation.
   TOP-LEVEL: abi_scratch_array_tail_prepare derives the recursive child's
   exact input from physical parent buffers and actual address execution. *)

Theorem abi_scratch_array_tail_prepare:
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\ abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input ei at av prepared src (SND ops) sb source_cap (d+off)
      (LENGTH (enc at av)) first last b cap actual /\
    eval_operand (FST ops) actual = SOME (n2w off) /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    abi_decoder_operand_live prepared.cs_next_var (FST ops) /\
    abi_decoder_operand_live prepared.cs_next_var (SND ops) /\
    abi_decoder_operand_live prepared.cs_next_var dyn_ptr /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  mp_tac (Q.INST [`st'` |-> `prepared`] abi_encode_array_tail_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `fp` |-> `abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`,
    `next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`]
    abi_scratch_address) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_input ei at av prepared src (SND ops) sb source_cap (d+off)
    (LENGTH (enc at av)) first last b cap actual` by
    (mp_tac (Q.INST [`dst` |-> `data_op:operand`, `child_dst` |-> `SND (ops:operand # operand)`]
       abi_scratch_child_input_address) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dyn_ptr actual = SOME (n2w slot)` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
