(* Precise execution of the array loop's real index initializer.
   TOP-LEVEL: abi_scratch_array_index preserves the complete source, processed
   output prefix and parent cursor while initializing a distinct index cursor. *)
Theory abiScratchArrayIndex
Ancestors
  abiScratchOwnedPrefix abiScratchPrefixReach abiScratchFootprint abiEncoderArrayInitCode
  abiEncoderComplexPrefix abiEncoderArrayFrame abiEncoderArrayPrefix abiEncoderMembersDefs
  abiEncoderInput abiEncoderInputFrame abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderLoop compileEnv valueEncoding contractABI venomState finite_map
  pred_set words list arithmetic

Theorem abi_scratch_array_index:
  abi_decode_index_init st = (index_ptr,st') /\ fn_has_code st st' func /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T parent_ptr parent_site parent_slot first lo st off initial /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual index_slot.
    abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs j d actual.vs_memory /\
    abi_encoder_cursor T parent_ptr parent_site parent_slot first lo st' off actual /\
    abi_encoder_cursor T index_ptr st.cs_next_id index_slot first st.cs_next_id st' 0 actual /\
    abi_encoder_complex_prefix_post [] index_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
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
  strip_tac >>
  `abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (index_ptr,st')` by
    asm_simp_tac bool_ss [GSYM abi_decode_index_init_complex_prefix] >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id` by decide_tac >>
  drule_all abi_scratch_owned_prefix_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `has_type (Array NONE ty) (ListV avs)` by
    (drule abi_encoder_input_typed >> simp[]) >>
  `abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap actual.vs_memory` by
    (drule_all abi_encoder_input_frame >> simp[]) >>
  `abi_encoder_array_prefix ty avs j d actual.vs_memory` by
    (drule_all abi_encoder_array_prefix_output_frame >> simp[]) >>
  `abi_encoder_cursor T parent_ptr parent_site parent_slot first lo st' off actual` by
    (drule_all abi_scratch_owned_prefix_parent >> simp[]) >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
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
  `fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual` by
    fs[abi_encoder_complex_prefix_post_def] >>
  qexistsl_tac [`actual`, `slot`] >> gvs[]
QED
