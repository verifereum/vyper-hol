(* Rich observations for the existing computed tail initializer execution. *)
Theory abiEncoderSharedArrayTailInit
Ancestors
  abiEncoderSharedArrayInit abiEncoderArrayTailInit abiScratchArrayTail
  abiEncoderMemberPhaseRaw abiEncoderComplexPrefix abiEncoderRegisteredEffect
  abiEncoderExtendSim abiDecoderAllocation abiDecoderReentry abiDecoderContract
  abiScratchEffect abiScratchOwnedPrefix abiScratchPrefixReach abiScratchPrefix
  abiEncoderSharedInputEffect abiEncoderSharedContract abiEncoderSharedArrayInput abiEncoderSharedArrayInitFrame
  abiEncoderArrayCursor abiEncoderMembersDefs abiEncoderArrayPrefix abiEncoderOpenInput
  abiEncoderSequence abiDecoderFootprint abiDecoderFrame abiScratchSubset pred_set valueEncoding contractABI
  context exprLoweringProps compileEnv emitHelper emitHelperProps venomInst venomState
  venomExecSemantics venomMemDefs instIdxIndep words list rich_list finite_map arithmetic

Theorem abi_encoder_array_tail_init_raw_observations:
  abi_encode_array_tail_init count_op asz st = (dp,final) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
  ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  simp[abi_encode_array_tail_init_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  gvs[abi_encoder_member_phase_raw_def, emitted_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  gvs[DROP_LENGTH_APPEND, run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
    exec_read1_def, eval_operand_def, AllCaseEqs()] >>
  drule abi_encoder_cursor_alloca_observations >> strip_tac >>
  gvs[Once step_inst_base_def, exec_pure2_def, eval_operand_def, AllCaseEqs()] >>
  gvs[Once step_inst_base_def, exec_write2_def, eval_operand_def, AllCaseEqs()] >>
  fs[update_var_def, mstore_def, write_memory_with_expansion_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_encoder_array_tail_init_raw_allocated:
  abi_encode_array_tail_init count_op asz st = (dp,final) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  !i r. FLOOKUP initial.vs_allocas i = SOME r ==> FLOOKUP ready.vs_allocas i = SOME r
Proof
  simp[abi_encode_array_tail_init_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  gvs[abi_encoder_member_phase_raw_def, emitted_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  gvs[DROP_LENGTH_APPEND, run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
    exec_read1_def, eval_operand_def, AllCaseEqs()] >>
  gvs[Once step_inst_base_def, exec_pure2_def, eval_operand_def, AllCaseEqs()] >>
  gvs[Once step_inst_base_def, exec_write2_def, eval_operand_def, AllCaseEqs()] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, mstore_def,
    write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE] >> Cases_on `st.cs_next_id = i` >> gvs[]
QED

Theorem abi_encoder_array_tail_init_raw_transport:
  abi_encode_array_tail_init count_op asz st = (dp,final) /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dp st.cs_next_var st.cs_next_id
    limit_st first last b cap initial ready
Proof
  strip_tac >> drule_all abi_encode_array_tail_init_sequence >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  gvs[abi_encoder_member_phase_raw_def] >>
  simp[abi_encoder_complex_prefix_post_inst_idx]
QED

Theorem abi_encoder_array_tail_init_raw_extend:
  abi_encode_array_tail_init count_op asz st = (dp,final) /\ fn_has_code st final func /\
  abi_encoder_member_phase_raw st final initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule abi_encode_array_tail_init_shape >> strip_tac >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED

Theorem abi_encoder_array_tail_init_raw_registered:
  abi_encode_array_tail_init count_op asz st = (dp,final) /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\ st.cs_next_id IN ids ==>
  abi_encoder_registered_effect ids outs initial ready /\ (alloca_inv initial ==> alloca_inv ready)
Proof
  strip_tac >> drule_all abi_encoder_array_tail_init_raw_transport >> strip_tac >>
  drule_all abi_encoder_array_tail_init_raw_observations >> strip_tac >>
  drule abi_encoder_array_tail_init_raw_allocated >> disch_then drule >> disch_tac >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (qx_choose_then `slot` strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> asm_rewrite_tac [] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  rpt strip_tac >>
  `a < slot \/ slot+32 <= a` by
    (first_x_assum (qspec_then `st.cs_next_id` mp_tac) >> simp[]) >>
  fs[abi_decode_frame_def] >> first_x_assum irule >> decide_tac
QED

Theorem abi_encoder_array_tail_init_raw_reach:
  abi_encode_array_tail_init count_op asz st = (dp,prepared) /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ prepared.cs_next_id <= last /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. abi_encoder_member_phase_raw st prepared initial actual /\
    abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dp st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id prepared.cs_next_id) b cap initial)
      initial actual
Proof
  strip_tac >> drule_all abi_scratch_array_tail_sequence >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  qexists_tac `raw with vs_inst_idx := LENGTH prepared.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def, abi_encoder_complex_prefix_post_inst_idx, abi_scratch_inst_idx] >>
  qexists_tac `raw` >> simp[]
QED

Theorem abi_encoder_shared_array_tail_prepare:
  abi_encode_array_tail_init count_op asz st = (dp,prepared) /\ fn_has_code st prepared func /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live st.cs_next_var count_op /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ prepared.cs_next_id <= last /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
      (prepared,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs j d actual.vs_memory /\
    abi_encoder_cursor T dp st.cs_next_id slot first st.cs_next_id prepared (LENGTH avs*asz) actual /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id prepared.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  strip_tac >> drule abi_encode_array_tail_init_shape >> strip_tac >>
  drule_all abi_encoder_array_tail_init_raw_reach >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `st.cs_next_id IN abi_decoder_ids first last /\
   st.cs_next_id IN abi_decoder_ids st.cs_next_id prepared.cs_next_id` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual` by
    (irule abi_scratch_prefix_effect >> simp[] >>
     qexistsl_tac [`dp`,`[(AbiPrimWord,LENGTH avs*asz,0,F)]`] >> simp[]) >>
  drule abi_encoder_shared_input_effect >> disch_then drule >> simp[] >> disch_tac >>
  `?slot. abi_encoder_cursor T dp st.cs_next_id slot first st.cs_next_id prepared
    (LENGTH avs*asz) actual` by
    (qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
       (qx_choose_then `slot` strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
     qexists_tac `slot` >> gvs[abi_encoder_cursor_def, abi_decoder_operand_live_def,
       abi_decoder_older_vars_def] >> rpt strip_tac >> decide_tac) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (prepared,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual` by
    (irule abi_encoder_shared_input_mono >> qexists_tac `st` >> simp[]) >>
  `abi_encoder_array_prefix ty avs j d actual.vs_memory` by
    (irule abi_encoder_shared_array_prefix_scratch >> goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `abi_encoder_shared_input _ _ _ _ _ _`)) >> simp[]) >>
  drule_all abi_encoder_array_tail_init_raw_registered >> strip_tac >>
  drule_all abi_encoder_array_tail_init_raw_extend >> disch_then (qspec_then `ctx` assume_tac) >>
  `actual.vs_current_bb = prepared.cs_current_bb /\
   actual.vs_inst_idx = LENGTH prepared.cs_current_insts` by
    (qpat_assum `abi_encoder_member_phase_raw _ _ _ _`
       (qx_choose_then `raw` strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_member_phase_raw_def]) >>
     drule_all abi_encoder_run_sequence_reach >>
     disch_then (qspec_then `ctx` strip_assume_tac) >> gvs[]) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (qx_choose_then `init_slot` strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  qexistsl_tac [`actual`,`slot`] >> gvs[]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared tail init admission, axiom or hypothesis"
  end) [abi_encoder_array_tail_init_raw_observations, abi_encoder_array_tail_init_raw_allocated,
    abi_encoder_array_tail_init_raw_transport, abi_encoder_array_tail_init_raw_extend,
    abi_encoder_array_tail_init_raw_registered, abi_encoder_array_tail_init_raw_reach,
    abi_encoder_shared_array_tail_prepare];
