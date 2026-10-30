(* One actual dynamic body and backedge advances the complete array state.
   TOP-LEVEL: abi_scratch_array_dynamic_round composes recursive encoding and
   the index update into one physical effect and containing-function simulation. *)
Theory abiScratchArrayDynamicRound
Ancestors
  abiScratchArrayDynamicMemory abiScratchArrayBackedge abiScratchEffect
  abiScratchEncoderContract abiEncoderArrayDynamicCode abiEncoderArrayBodyMemory
  abiEncoderArrayLayout abiEncoderMembersDefs abiEncoderInput abiEncoderArrayPrefix
  abiDecoderAllocation abiDecoderFootprint abiDecoderLoop abiDecoderReentry abiDecoderContract
  compileEnv valueEncoding contractABI venomState venomInst words list arithmetic

Theorem abi_scratch_array_dynamic_round:
  abi_scratch_encoder ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = end_st.cs_current_insts ++ abi_decode_backedge_insts end_st.cs_next_id
    (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString end_st.cs_next_var)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first lo owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  site < cursor_site /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id+3 <= last /\
  end_st.cs_next_var+1 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first lo owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  drule abi_encode_array_dynamic_body_index >> disch_tac >>
  `owner_st.cs_next_id <= last /\ end_st.cs_next_id <= last /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var /\
    owner_st.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`index_site` |-> `site:num`, `index_slot` |-> `slot:num`,
    `site` |-> `cursor_site:num`, `slot` |-> `cursor_slot:num`,
    `off` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j (avs:abi_value list)))`]
    abi_scratch_array_dynamic_body_memory) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial encoded` >>
  qpat_assum `out = Var _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encoder_input_typed >> disch_tac >>
  `j <= LENGTH avs` by decide_tac >> drule_all abi_encoder_array_prefix_types >> strip_tac >>
  qpat_assum `abi_scratch_effect _ _ cursor_site end_st.cs_next_id _ _ _ _ _ _ initial encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  mp_tac (Q.INST [`initial` |-> `encoded:venom_state`, `k` |-> `SUC j`, `n` |-> `LENGTH (avs:abi_value list)`,
    `off` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) (avs:abi_value list)))`,
    `prefix` |-> `end_st.cs_current_insts`, `id` |-> `end_st.cs_next_id`, `next` |-> `end_st.cs_next_var`,
    `iv` |-> `STRING #"%" (toString st.cs_next_var)`] abi_scratch_array_backedge_memory) >>
  impl_tac >- full_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  `first <= site` by fs[abi_encoder_cursor_def] >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial encoded` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `cursor_site`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `site+1`, `site`, `end_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `encoded` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED
