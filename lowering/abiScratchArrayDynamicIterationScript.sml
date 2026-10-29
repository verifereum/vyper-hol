(* The real recursive body advances the complete output and source invariants.
   TOP-LEVEL: abi_scratch_array_dynamic_iteration extends the encoded prefix,
   updates the tail offset and retains complete source data and separation. *)
Theory abiScratchArrayDynamicIteration
Ancestors
  abiScratchArrayDynamicBody abiScratchPrefix abiScratchInput abiScratchSubset
  abiScratchEncoderContract abiEncoderArrayDynamicIteration abiEncoderArrayLayout
  abiEncoderArrayPrefix abiEncoderInput abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI
  venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_array_dynamic_iteration:
  abi_scratch_encoder ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
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
  ?actual. abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      st src dst sb source_cap d output_size first last b cap actual /\
    mem_word_at slot actual.vs_memory = n2w (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_scratch_array_dynamic_body_reach >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_scratch_array_body_bounds >> strip_tac >>
  `abi_decoder_ids site end_st.cs_next_id SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids site end_st.cs_next_id) b cap initial)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
  qpat_assum `asz = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch (abi_decoder_ids site end_st.cs_next_id) b cap initial`]
    abi_scratch_array_dynamic_step) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei (abi_member_head_size ty) msz T`,
    `at` |-> `Array NONE ty`, `av` |-> `ListV avs`, `sz` |-> `output_size:num`,
    `lo` |-> `site:num`, `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`]
    abi_scratch_input_effect) >> impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  drule_all abi_encoder_array_tail_sum_suc >> disch_tac >>
  qexists_tac `actual` >> full_simp_tac bool_ss [ADD_ASSOC]
QED
