(* Actual computed tail-cursor initialization preserves the source and empty output prefix. *)
Theory abiEncoderArrayTailInitPrepare
Ancestors
  abiEncoderArrayTailInitSequence abiEncoderArrayTailInitCode abiEncoderSequenceReach
  abiEncoderComplexPrefixEffect abiEncoderComplexPrefixReach abiEncoderArrayIndexPrepare
  abiEncoderArrayMemory abiEncoderArrayExitInputs abiEncoderMembersDefs abiEncoderChildInputs
  abiDecoderEffect abiDecoderAllocation abiDecoderPrimitiveLoopFrames abiDecoderFrame abiDecoderContract abiDecoderReentry
  abiDecoderLoop fragExec compileEnv valueEncoding contractABI venomState venomInst words list arithmetic pred_set

Theorem abi_encode_array_tail_init_reach:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  drule_all abi_encode_array_tail_init_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK encoded` >>
  `~encoded.vs_halted` by fs[abi_encoder_complex_prefix_post_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >> gvs[]
QED

Theorem abi_encoder_array_tail_init_prepare:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,owner_st) /\ fn_has_code st owner_st func /\
  abi_encoder_array_memory ei asz msz T ty avs st src dst sb source_cap d output_size b cap 0 initial /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ lo <= st.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_array_memory ei asz msz T ty avs owner_st src dst sb source_cap d output_size b cap 0 ready /\
    abi_encoder_cursor T dyn_ptr st.cs_next_id slot first lo owner_st
      (LENGTH avs*abi_member_head_size ty) ready /\
    abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = owner_st.cs_current_bb /\ ready.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_init_shape >> strip_tac >> drule abi_encoder_array_exit_inputs >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (avs:abi_value list)`, `st'` |-> `owner_st`]
    abi_encode_array_tail_init_reach) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial ready` by
    (mp_tac (Q.INST [`infos` |-> `[(AbiPrimWord,LENGTH (avs:abi_value list)*asz,0,F)]`,
      `site` |-> `st.cs_next_id`, `next` |-> `st.cs_next_var`, `outsz` |-> `output_size:num`,
      `actual` |-> `ready:venom_state`] abi_encoder_complex_prefix_effect) >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ ready`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS) o
      PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_decoder_operand_live owner_st.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `abi_encoder_cursor T dyn_ptr st.cs_next_id slot first lo owner_st
    (LENGTH avs*abi_member_head_size ty) ready` by
    (asm_simp_tac (srw_ss()) [abi_encoder_cursor_def] >> decide_tac) >>
  `abi_decode_footprint_frame [(slot,32)] initial ready` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  `abi_footprint_disjoint d output_size [(slot,32)]` by
    (simp_tac (srw_ss()) [abi_footprint_disjoint_def] >> decide_tac) >>
  `abi_encoder_array_memory ei asz msz T ty avs st src dst sb source_cap d output_size b cap 0 ready` by
    (mp_tac (Q.INST [`dyn` |-> `T`, `j` |-> `0:num`, `fp` |-> `[(slot,32)]`,
      `lo` |-> `st.cs_next_id`, `actual` |-> `ready:venom_state`] abi_encoder_array_memory_scratch) >>
     impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  `st.cs_next_var <= owner_st.cs_next_var` by decide_tac >>
  drule_all abi_encoder_array_memory_mono >> strip_tac >>
  qexistsl_tac [`ready`, `slot`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_TAIL_INIT_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder tail initialization preparation not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayTailInitPrepare");
