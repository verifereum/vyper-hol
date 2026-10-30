(* Finish through the parent cursor after the recursively executed array loop.
   TOP-LEVEL: abi_scratch_array_finish_protected derives preservation of the
   parent slot and completed output from the initial physical scratch footprint. *)
Theory abiScratchArrayFinishProtected
Ancestors
  abiScratchArrayParent abiScratchCursor abiScratchEncoderContract abiScratchFootprint
  abiEncoderArrayCursor abiEncoderMembersDefs abiDecoderAllocation abiDecoderFootprint
  abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI
  venomState words list arithmetic

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
