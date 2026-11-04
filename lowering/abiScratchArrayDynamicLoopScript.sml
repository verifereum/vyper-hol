Theory abiScratchArrayDynamicLoop
Ancestors
  abiScratchArrayIndex abiScratchArrayTail abiScratchCompose abiScratchFootprint
  abiEncoderArrayDynamicLoop abiEncoderComplexPrefix abiEncoderMembersDefs abiEncoderInput
  abiEncoderArrayPrefix abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderLoop compileEnv valueEncoding contractABI venomState finite_map
  pred_set words list arithmetic abiScratchArrayInitEffects abiScratchEncoderContract
  abiScratchEffect abiScratchArrayLoopRun abiEncoderArrayLoopCode abiDecoderContract venomInst

(* ===== Scratch Array Dynamic Init ===== *)

(* Complete execution of the actual dynamic-array loop initializer.
   TOP-LEVEL: abi_scratch_array_dynamic_init composes index and tail allocation,
   preserving source data, processed output, parent cursor and older operands. *)

Theorem abi_scratch_array_dynamic_init:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\
  fn_has_code start owner_st func /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ owner_st.cs_next_id <= last /\
  owner_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T parent_ptr parent_site parent_slot first lo start off initial /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual index_slot tail_slot.
    abi_encoder_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T parent_ptr parent_site parent_slot first lo owner_st off actual /\
    abi_encoder_cursor T (FST ptrs) start.cs_next_id index_slot first start.cs_next_id
      owner_st 0 actual /\
    abi_encoder_cursor T (SND ptrs) (start.cs_next_id+2) tail_slot first (start.cs_next_id+2)
      owner_st (LENGTH avs*asz) actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_footprint_disjoint sb source_cap
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
    (!op. abi_decoder_operand_live start.cs_next_var op ==>
      eval_operand op actual = eval_operand op initial) /\
    actual.vs_current_bb = owner_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
  `after_index.cs_next_var <= limit_st.cs_next_var /\ after_index.cs_next_id <= last /\
   first <= after_index.cs_next_id /\ start.cs_next_var <= after_index.cs_next_var` by decide_tac >>
  drule_all abi_scratch_array_index >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial indexed` >>
  rename1 `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id after_index 0 indexed` >>
  `eval_operand count_op indexed = SOME (n2w (LENGTH avs))` by
    (qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >> simp[]) >>
  `abi_decoder_operand_live after_index.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  drule_all (Q.INST [`initial` |-> `indexed:venom_state`] abi_scratch_array_tail_input) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func indexed actual` >>
  rename1 `abi_encoder_cursor T dyn_ptr after_index.cs_next_id tail_slot first after_index.cs_next_id
    owner_st (LENGTH avs*asz) actual` >>
  `abi_encoder_cursor T parent_ptr parent_site parent_slot first lo owner_st off actual` by
    (qpat_assum `!op site slot lo off. _` drule_all >> simp[]) >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id owner_st 0 actual` by
    (qpat_assum `!op site slot lo off. _` drule_all >> simp[]) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  `abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual` by
    (drule_all abi_scratch_frame_trans >> simp[]) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (drule_all abi_scratch_evolution_trans >> simp[]) >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    eval_operand op actual = eval_operand op initial` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live after_index.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
     qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ initial indexed`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
     qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ indexed actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
     asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `index_slot`, `tail_slot`] >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `indexed` >> simp[]
QED

(* ===== Prepare ===== *)

(* Both actual loop initializers establish the precise executable loop entry.
   TOP-LEVEL: abi_scratch_array_dynamic_init_prepare retains complete buffers,
   initializes distinct index/tail cursors and composes their owned effects. *)

Theorem abi_scratch_array_dynamic_init_prepare:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\ fn_has_code start owner_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\ abi_decoder_operand_live start.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?ready index_slot tail_slot.
    abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap ready /\
    abi_encoder_array_prefix ty avs 0 d ready.vs_memory /\
    abi_encoder_cursor T (FST ptrs) start.cs_next_id index_slot first start.cs_next_id owner_st 0 ready /\
    abi_encoder_cursor T (SND ptrs) (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
      (LENGTH avs*abi_member_head_size ty) ready /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = owner_st.cs_current_bb /\ ready.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
  `after_index.cs_next_var <= limit_st.cs_next_var /\ after_index.cs_next_id <= last /\
   first <= after_index.cs_next_id /\ owner_st.cs_next_id <= last /\
   start.cs_next_var <= after_index.cs_next_var` by decide_tac >>
  `asz = abi_member_head_size ty` by fs[abi_scratch_input_def, abi_encoder_array_input_iff] >>
  mp_tac (Q.INST [`st` |-> `start`, `st'` |-> `after_index`, `active` |-> `T`, `index_ptr` |-> `ip:operand`]
    abi_scratch_array_index_prepare) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial indexed` >>
  rename1 `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id after_index 0 indexed` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial indexed`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `eval_operand count_op indexed = SOME (n2w (LENGTH avs))` by
    (qpat_assum `!op w. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live after_index.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `after_index`, `st'` |-> `owner_st`, `active` |-> `T`,
    `initial` |-> `indexed:venom_state`] abi_scratch_array_tail_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func indexed ready` >>
  rename1 `abi_encoder_cursor T dyn_ptr after_index.cs_next_id tail_slot first after_index.cs_next_id
    owner_st (LENGTH avs*asz) ready` >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id owner_st 0 ready` by
    (qpat_assum `!op cursor_site cursor_slot cursor_lo off. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_encoder_cursor T dyn_ptr (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
    (LENGTH avs*abi_member_head_size ty) ready` by
    (gvs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial indexed` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `after_index.cs_next_id`, `start.cs_next_id`, `start.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap indexed ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `owner_st.cs_next_id`, `after_index.cs_next_id`, `after_index.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `indexed` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`ready`, `index_slot`, `tail_slot`] >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `indexed` >> simp[]
QED

(* Execute the complete actual dynamic-element encoder loop with physical frames.
   TOP-LEVEL: abi_scratch_array_dynamic_loop composes both initializers, entry,
   all recursive iterations and the real exit reload/length computation. *)
Theorem abi_scratch_array_dynamic_loop:
  abi_scratch_encoder ei /\ compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
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
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= hi /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var /\ start.cs_next_id < start.cs_next_id+2` by
    (qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >> decide_tac) >>
  drule_all abi_scratch_array_dynamic_init_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (qpat_assum `!op w. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`ip` |-> `FST (ptrs:operand # operand)`, `dyn_ptr` |-> `SND (ptrs:operand # operand)`,
    `site` |-> `start.cs_next_id`, `slot` |-> `index_slot:num`, `cursor_site` |-> `start.cs_next_id+2`,
    `cursor_slot` |-> `tail_slot:num`, `initial` |-> `ready:venom_state`]
    abi_scratch_array_dynamic_loop_run) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `start.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED
