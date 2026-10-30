(* Protect the parent cursor across the shared loop, then reuse scalar finish. *)
Theory abiEncoderSharedArrayFinishProtected
Ancestors
  abiEncoderSharedArrayFinishRun abiScratchCursor abiScratchFootprint
  abiEncoderArrayCursor abiEncoderMembersDefs abiScratchEncoderContract abiScratchEffect
  abiEncoderRegisteredEffect abiEncoderExtendSim abiDecoderAllocation abiDecoderFootprint
  abiDecoderReentry abiDecoderContract compileEnv valueEncoding contractABI venomState words list arithmetic

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
