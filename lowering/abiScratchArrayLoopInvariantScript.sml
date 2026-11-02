(* Complete source, output and cursor observations at an encoder loop entry.
   TOP-LEVEL: abi_scratch_array_loop_inv and its composition rule retain the
   original physical scratch footprint across repeated allocation-site reuse. *)
Theory abiScratchArrayLoopInvariant
Ancestors
  abiScratchEncoderContract abiScratchEffect abiEncoderArrayPrefix abiEncoderArrayBodyCode
  abiEncoderMembersDefs abiEncoderInput abiDecoderAllocation abiDecoderReentry compileEnv
  valueEncoding contractABI venomState words list arithmetic

Definition abi_scratch_array_loop_inv_def:
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label j origin s <=>
    abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap s /\
    abi_encoder_array_prefix ty avs j d s.vs_memory /\
    abi_encoder_cursor T ip site slot first site owner_st j s /\
    abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) s /\
    (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
    eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
    s.vs_current_bb = label /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin s
End

Theorem abi_scratch_array_loop_inv_facts:
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label j origin s ==>
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs /\ LENGTH avs < dimword (:256) /\
  first <= site /\ fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s
Proof
  simp_tac bool_ss [abi_scratch_array_loop_inv_def, abi_scratch_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_input_typed >> disch_tac >>
  `j <= LENGTH avs` by fs[abi_encoder_array_prefix_def] >>
  drule_all abi_encoder_array_prefix_types >> strip_tac >>
  fs[abi_scratch_effect_def, abi_encoder_cursor_def]
QED

Theorem abi_scratch_array_loop_inv_advance:
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label j origin initial /\
  abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap actual /\
  abi_encoder_array_prefix ty avs k d actual.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st k actual /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE k avs))) actual /\
  hi <= last /\ actual.vs_current_bb = next_label /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted ==>
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op next_label k origin actual
Proof
  simp_tac bool_ss [abi_scratch_array_loop_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `first <= site` by fs[abi_encoder_cursor_def] >>
  `eval_operand count_op actual = SOME (n2w (LENGTH avs))` by
    (mp_tac (Q.INST [`op` |-> `count_op:operand`, `w` |-> `n2w (LENGTH (avs:abi_value list)):bytes32`,
      `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`, `lo` |-> `site:num`,
      `sz` |-> `output_size:num`, `next` |-> `owner_st.cs_next_var`] abi_scratch_effect_operand) >>
     asm_simp_tac bool_ss []) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED
