(* Read the actual exit length after the precise invariant reaches the last index.
   TOP-LEVEL: abi_scratch_array_dynamic_scalar_exit returns the complete ABI
   bytes and length with a composed physical effect from the loop origin.
   Helper: the completed prefix identifies the final tail cursor exactly. *)
Theory abiScratchArrayLoopExit
Ancestors
  abiScratchArrayLoopInvariant abiScratchAddress abiScratchEffect abiScratchEncoderContract
  abiEncoderArrayExit abiEncoderArrayCursor abiEncoderArrayLayout abiEncoderArrayPrefix
  abiEncoderMembersDefs abiEncoderInput abiDecodeRanges abiDecoderDynamicLoopSetup
  abiDecoderLoop abiDecoderReentry abiDecoderContract compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_scratch_array_loop_output:
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin actual ==>
  mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH (enc (Array NONE ty) (ListV avs))-32) actual
Proof
  strip_tac >> drule abi_scratch_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  drule_all abi_encoder_array_prefix_complete >> disch_tac >>
  drule canonical_array_length >> strip_tac >>
  `LENGTH (enc (Array NONE ty) (ListV avs))-32 =
    LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) avs)` by
    (full_simp_tac bool_ss [] >> decide_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [TAKE_LENGTH_ID]) >>
  asm_simp_tac (srw_ss()) [Excl "enc_def"]
QED

Theorem abi_scratch_array_dynamic_scalar_exit:
  abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin initial /\
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) /\ fn_has_code st final func /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\ hi <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ label = st.cs_current_bb /\ st.cs_current_insts = [] ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_array_loop_output >> strip_tac >>
  drule abi_scratch_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  mp_tac (Q.INST [`cursor_op` |-> `dyn_ptr:operand`, `site` |-> `cursor_site:num`, `slot` |-> `cursor_slot:num`,
    `off` |-> `LENGTH (enc (Array NONE ty) (ListV avs))-32`, `st` |-> `owner_st`,
    `s` |-> `initial:venom_state`, `lo` |-> `site:num`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH (enc (Array NONE ty) (ListV avs))-32) initial`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `abi_decoder_operand_live st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  `32+(LENGTH (enc (Array NONE ty) (ListV avs))-32) = LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule canonical_array_length >> strip_tac >> full_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.INST [`src_word` |-> `n2w sb:bytes32`, `slot` |-> `cursor_slot:num`,
    `offset` |-> `LENGTH (enc (Array NONE ty) (ListV avs))-32`] abi_encode_array_dynamic_exit_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `site:num`, `next` |-> `st.cs_next_var`, `sz` |-> `output_size:num`]
    abi_scratch_address_effect) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `site`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> fs[abi_decoder_address_frame_def]
QED
