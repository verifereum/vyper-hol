Theory abiEncoderSharedArrayOuter
Ancestors
  abiEncoderSharedArrayIndexInit abiEncoderSharedArrayParent abiEncoderArrayDynamicLoop
  abiEncoderSharedArrayInitFrame abiEncoderSharedContract abiEncoderRegisteredEffect
  abiEncoderExtendSim abiEncoderArrayHeaderMemory abiEncoderMembersDefs abiEncoderArrayPrefix
  abiScratchCursor abiScratchEffect abiScratchEncoderContract abiDecoderAllocation
  abiDecoderReentry abiDecoderContract compileEnv valueEncoding contractABI venomState words
  list arithmetic pred_set abiEncoderSharedArrayRun abiEncoderArrayLoopCode
  abiEncoderArrayParent abiEncoderArrayContext abiEncoderArrayPhases abiEncoderMemberPhaseRaw
  abiEncoderMemberPhaseEffect abiDecoderFootprint abiDecoderFrameCompose abiDecoderFrame
  abiDecoderDynamicLoopSetup exprLoweringProps emitHelper emitHelperProps venomInst
  venomExecSemantics venomMemDefs instIdxIndep rich_list abiEncoderSequence abiScratchFootprint
  abiDecoderProtectedScratch abiScratchPhaseCompose

(* Dynamic initializer assembly: shared index and tail allocation boundaries. *)
Theorem abi_encoder_shared_array_dynamic_init:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\
  fn_has_code start owner_st func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual index_slot tail_slot.
    abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
      (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T (FST ptrs) start.cs_next_id index_slot first start.cs_next_id owner_st 0 actual /\
    abi_encoder_cursor T (SND ptrs) (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
      (LENGTH avs*abi_member_head_size ty) actual /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = owner_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
  `after_index.cs_next_var <= limit_st.cs_next_var /\ after_index.cs_next_id <= last /\
   first <= after_index.cs_next_id /\ owner_st.cs_next_id <= last /\
   start.cs_next_var <= after_index.cs_next_var` by decide_tac >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  qpat_x_assum `T <=> is_dynamic ty` (assume_tac o REWRITE_RULE [EQ_CLAUSES]) >>
  drule_all abi_encoder_shared_array_index_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `indexed` (qx_choose_then `index_slot` strip_assume_tac))) >>
  `eval_operand count_op indexed = SOME (n2w (LENGTH avs))` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_decoder_operand_live after_index.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `fresh_vars_wrt limit_st indexed /\ abi_decoder_budget first last b cap indexed` by
    fs[abi_scratch_effect_def] >>
  drule_all abi_encoder_shared_array_tail_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` (qx_choose_then `tail_slot` strip_assume_tac))) >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id after_index 0 actual` by
    (qpat_assum `abi_encoder_shared_input _ (after_index,_,_) _ _ _ indexed`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
     irule abi_scratch_cursor_protected >>
     goal_assum (drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id owner_st 0 actual` by
    (irule abi_encoder_cursor_mono >> qexists_tac `after_index` >> simp[]) >>
  `abi_encoder_cursor T dyn_ptr (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
    (LENGTH avs*abi_member_head_size ty) actual` by
    (gvs[abi_encoder_cursor_def, Excl "enc_def"] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial indexed` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap indexed actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `indexed` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial indexed` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] indexed actual` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `indexed` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `indexed` >> asm_rewrite_tac []) >>
  qexistsl_tac [`actual`,`index_slot`,`tail_slot`] >> gvs[Excl "enc_def"]
QED

(* Dynamic loop assembly through shared initialization and prepared execution. *)
Theorem abi_encoder_shared_array_dynamic_loop:
  abi_encoder_shared ei /\
  compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_id <= hi /\
   owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var` by
    (fs[abi_encoder_array_loop_code_def] >> decide_tac) >>
  drule_all abi_encoder_shared_array_dynamic_init >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready`
    (qx_choose_then `slot` (qx_choose_then `tail_slot` strip_assume_tac)))) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    fs[abi_scratch_effect_def] >>
  `mem_word_at d ready.vs_memory = n2w (LENGTH avs)` by
    fs[abi_encoder_array_prefix_def, Excl "enc_def"] >>
  `start.cs_next_id < start.cs_next_id+2` by decide_tac >>
  drule_all (Q.INST [`active` |-> `T`] abi_encoder_shared_array_prepared_complete
    |> REWRITE_RULE [COND_CLAUSES, EQ_CLAUSES, AND_CLAUSES, OR_CLAUSES]) >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap ready actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Static loop assembly through shared initialization and prepared execution. *)
Theorem abi_encoder_shared_array_static_loop:
  abi_encoder_shared ei /\ abi_encoder_static_leaf ei /\
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_id <= hi /\
   owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var` by
    (fs[abi_encoder_array_loop_code_def] >> decide_tac) >>
  drule_all abi_encoder_shared_array_index_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready` (qx_choose_then `slot` strip_assume_tac))) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    fs[abi_scratch_effect_def] >>
  `mem_word_at d ready.vs_memory = n2w (LENGTH avs)` by
    fs[abi_encoder_array_prefix_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`active` |-> `F`, `initial` |-> `ready:venom_state`,
    `site` |-> `start.cs_next_id`] abi_encoder_shared_array_prepared_complete) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial ready` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap ready actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial ready` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Dispatch the two existing shared generated-loop assemblies. *)
Theorem abi_encoder_shared_array_selected_loop:
  abi_encoder_shared ei /\ (~active ==> abi_encoder_static_leaf ei) /\
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final)
   else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final)) /\
  fn_has_code start final func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  Cases_on `active` >> simp_tac bool_ss [COND_CLAUSES, NOT_CLAUSES, IMP_CLAUSES] >> strip_tac
  >- (drule_all abi_encoder_shared_array_dynamic_loop >> simp[]) >>
  drule_all abi_encoder_shared_array_static_loop >> simp[]
QED

(* Fixed parent bookkeeping at a supplied raw endpoint; no recursive execution. *)
Theorem abi_encoder_array_finish_raw_transport:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (old_word+size_word) /\ mload slot ready = old_word+size_word /\
  fresh_vars_wrt limit_st ready /\ abi_decode_frame slot 32 initial ready /\
  ready.vs_allocas = initial.vs_allocas /\ ready.vs_alloca_next = initial.vs_alloca_next /\
  ready.vs_halted = initial.vs_halted /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op ready = SOME w)
Proof
  strip_tac >> drule_all abi_encode_array_finish_sequence >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def, eval_op_inst_idx, fresh_vars_wrt_def,
      abi_decode_frame_def, mload_def] >> metis_tac[]
QED

Theorem abi_encoder_array_finish_opcodes:
  abi_encode_array_finish parent_ptr size_op st = (out,final) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
    (emitted_insts st final)
Proof
  simp[abi_encode_array_finish_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_array_finish_registered:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\
  id IN ids /\ FLOOKUP initial.vs_allocas id = SOME (slot,32) ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  strip_tac >> drule_all abi_encoder_array_finish_raw_transport >> strip_tac >>
  `ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
   ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests` by
    (irule abi_encoder_member_phase_globals >> goal_assum (drule_at Any) >>
     drule abi_encoder_array_finish_opcodes >> simp[]) >>
  conj_tac
  >- (simp_tac bool_ss [abi_encoder_registered_effect_def] >>
      gvs[abi_decode_frame_def] >> rpt strip_tac >>
      `a < slot \/ slot+32 <= a` by
        (qpat_x_assum `!i b sz. _` (qspecl_then [`id`,`slot`,`32`] mp_tac) >> simp[]) >>
      first_x_assum irule >> decide_tac) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_array_finish_extend:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  abi_encoder_member_phase_raw st final initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule abi_encode_array_finish_shape >> strip_tac >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED

Theorem abi_encoder_shared_array_finish_effect:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial ready /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready) /\ abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule_all abi_encoder_array_finish_raw_transport >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial ready` by
    fs[abi_decode_frame_footprint] >>
  `site IN abi_decoder_ids lo hi` by simp[abi_decoder_ids_def] >>
  drule_all abi_encoder_array_finish_registered >>
  disch_then (qspecl_then [`[(d,sz)]`] strip_assume_tac) >>
  drule_all abi_encoder_array_finish_extend >> disch_then (qspec_then `ctx` assume_tac) >>
  asm_simp_tac bool_ss [] >> irule abi_scratch_single_write >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  qexistsl_tac [`site`,`slot`] >> asm_rewrite_tac []
QED

Theorem abi_encoder_array_finish_preserves_output:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\
  mem_bytes_at d len initial.vs_memory = bytes /\
  abi_footprint_disjoint d len [(slot,32)] ==>
  mem_bytes_at d len ready.vs_memory = bytes /\
  eval_operand out ready = SOME (n2w len) /\ mload slot ready = n2w len
Proof
  strip_tac >> drule_all abi_encoder_array_finish_raw_transport >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial ready` by
    fs[abi_decode_frame_footprint] >>
  drule_all abi_decode_footprint_frame_slice >> simp[]
QED

(* Execute the existing scalar finish sequence and attach rich observations. *)
Theorem abi_encoder_shared_array_finish_run:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  mem_bytes_at d len initial.vs_memory = bytes /\ len <= sz /\
  abi_footprint_disjoint d sz (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\
    eval_operand out actual = SOME (n2w len) /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ _`
      (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> decide_tac) >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_scratch_registered_member >> simp[] >> qexists_tac `site` >> simp[]) >>
  `abi_footprint_disjoint d len [(slot,32)]` by
    (fs[abi_footprint_disjoint_def] >> rpt strip_tac >> res_tac >> decide_tac) >>
  drule_all abi_encode_array_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule abi_encode_array_finish_shape >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `abi_encoder_member_phase_raw st final initial actual` by
    (simp[abi_encoder_member_phase_raw_def] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_encoder_array_finish_preserves_output >> strip_tac >>
  drule_all abi_encoder_shared_array_finish_effect >>
  disch_then (qspecl_then [`sz`,`d`,`ctx`] strip_assume_tac) >>
  qexists_tac `actual` >> gvs[]
QED

(* Protect the parent cursor across the shared loop, then reuse scalar finish. *)
Theorem abi_encoder_shared_array_finish_protected:
  abi_encoder_cursor T parent_ptr site slot first site loop_st 0 ready /\
  abi_scratch_effect first last loop_st.cs_next_id loop_end.cs_next_id loop_st.cs_next_var
    limit_st d sz b cap ready encoded /\
  abi_decoder_budget first last b cap ready /\
  abi_footprint_disjoint d sz (abi_decoder_child_scratch (abi_decoder_ids first last) b cap ready) /\
  loop_st.cs_next_var <= loop_end.cs_next_var /\ loop_st.cs_next_id <= loop_end.cs_next_id /\
  site < loop_st.cs_next_id /\ loop_end.cs_next_id <= last /\ site < final.cs_next_id /\
  abi_encode_array_finish parent_ptr size_op loop_end = (out,final) /\ fn_has_code loop_end final func /\
  eval_operand size_op encoded = SOME (n2w len) /\ abi_decoder_operand_live loop_end.cs_next_var size_op /\
  mem_bytes_at d len encoded.vs_memory = bytes /\ len <= sz /\
  final.cs_next_var <= limit_st.cs_next_var /\ ~encoded.vs_halted /\
  encoded.vs_current_bb = loop_end.cs_current_bb /\ encoded.vs_inst_idx = LENGTH loop_end.cs_current_insts ==>
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\ eval_operand out actual = SOME (n2w len) /\
    abi_scratch_effect first last site final.cs_next_id loop_end.cs_next_var limit_st d sz b cap encoded actual /\
    abi_encoder_registered_effect (abi_decoder_ids site final.cs_next_id) [(d,sz)] encoded actual /\
    (alloca_inv encoded ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `first <= loop_st.cs_next_id /\ site < last` by
    (fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_encoder_cursor T parent_ptr site slot first site loop_st 0 encoded` by
    (irule abi_scratch_cursor_protected >>
     goal_assum (drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_cursor T parent_ptr site slot first site loop_end 0 encoded` by
    (irule abi_encoder_cursor_mono >> qexists_tac `loop_st` >> asm_rewrite_tac []) >>
  qpat_assum `abi_encoder_cursor T _ _ _ _ _ loop_end _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `fresh_vars_wrt limit_st encoded /\ abi_decoder_budget first last b cap encoded` by
    fs[abi_scratch_effect_def] >>
  `abi_footprint_disjoint d sz (abi_decoder_child_scratch (abi_decoder_ids first last) b cap encoded)` by
    (irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `ready` >> fs[abi_scratch_effect_def]) >>
  drule_all (Q.INST [`lo` |-> `site:num`, `hi` |-> `final.cs_next_id`]
    abi_encoder_shared_array_finish_run) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[]
QED

(* Complete array construction by composing established rich phase boundaries. *)
Theorem abi_encoder_shared_array_outer:
  abi_encoder_shared ei /\ (~active ==> abi_encoder_static_leaf ei) /\
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) start = (out,final) /\
  fn_has_code start final func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id final.cs_next_id start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_context >> strip_tac >>
  `loop_st.cs_next_id <= last /\ loop_end.cs_next_id <= last /\
   loop_st.cs_next_var <= limit_st.cs_next_var /\ loop_end.cs_next_var <= limit_st.cs_next_var /\
   start.cs_next_id < loop_st.cs_next_id /\ start.cs_next_id < final.cs_next_id /\
   first <= loop_st.cs_next_id /\ start.cs_next_var <= loop_st.cs_next_var /\
   loop_end.cs_next_id <= final.cs_next_id` by decide_tac >>
  drule_all abi_encoder_shared_array_parent_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready` (qx_choose_then `slot` strip_assume_tac))) >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by fs[abi_scratch_effect_def] >>
  drule_all (Q.INST [`hi` |-> `final.cs_next_id`] abi_encoder_shared_array_selected_loop
    |> REWRITE_RULE [LESS_EQ_REFL, AND_CLAUSES]) >>
  disch_then (qspec_then `ctx` (qx_choose_then `encoded` strip_assume_tac)) >>
  qpat_assum `abi_encoder_shared_input _ (loop_st,_,_) _ _ _ ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  drule_all abi_encoder_shared_array_finish_protected >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `start.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  drule_all abi_scratch_phase_compose >> disch_tac >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] initial ready` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] ready encoded` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] initial encoded` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `encoded` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial encoded` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `encoded` >> asm_rewrite_tac []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
