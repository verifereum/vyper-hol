Theory abiScratchArrayStaticLoop
Ancestors
  abiScratchStatic abiScratchArrayPrepare abiScratchArrayEntry abiScratchAfterAddress
  abiScratchFrameCompose abiScratchEncoderContract abiScratchEffect abiEncoderArrayBodyCode
  abiEncoderAdmissible abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderDynamicLoopSetup abiDecoderLoop abiDecoderContract compileEnv
  valueEncoding contractABI venomState pred_set words list arithmetic abiScratchInput
  abiScratchCursor abiEncoderArrayHeaderMemory abiEncoderMembersDefs abiEncoderArrayPrefix
  abiScratchArrayBackedge abiScratchFootprint abiEncoderArrayRound abiEncoderArrayFrame
  abiEncoderInput abiDecoderArrayBackedge venomInst finite_map abiScratchArrayLoopHeader
  abiScratchArrayLoopInvariant abiScratchArrayFiniteLoop abiEncoderArrayLoopCode
  abiEncoderArrayLoopDynamicStep abiScratchArrayLoopRun abiScratchArrayStaticExit
  venomExecSemantics abiScratchArrayInitEffects

(* Execute the real static-element array body with complete physical resources.
   TOP-LEVEL: abi_scratch_array_static_body_reach composes actual address setup
   and static child execution. Helper: the selected static element fits its head. *)
Theorem abi_scratch_array_static_bounds:
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\ j < LENGTH avs ==>
  has_type (Array NONE ty) (ListV avs) /\ ~is_dynamic ty /\ asz = abi_member_head_size ty /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\ 32 <= output_size /\
  j*asz+LENGTH (enc ty (EL j avs)) <= output_size-32
Proof
  strip_tac >> drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  gvs[Excl "enc_def"] >> decide_tac
QED

Theorem abi_scratch_array_static_body_reach:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+32+j*asz) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    eval_operand out actual = SOME (n2w j) /\
    abi_decode_footprint_frame
      ((d+32+j*asz,LENGTH (enc ty (EL j avs)))::
        abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id /\
   st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all abi_scratch_array_static_bounds >> strip_tac >>
  mp_tac (Q.INST [`active` |-> `F`] abi_scratch_array_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `prepared`, `initial` |-> `ready:venom_state`, `out` |-> `ignored`,
    `src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `dst` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`,
    `head` |-> `SND (SND (coords:(operand # operand) # (operand # operand)))`,
    `at` |-> `ty:abi_type`, `av` |-> `EL j (avs:abi_value list)`, `offset` |-> `j*asz`,
    `sb` |-> `sb+32+j*msz`, `source_cap` |-> `msz:num`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_scratch_static_info_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `eval_operand (FST (FST coords)) actual = SOME (n2w j)` by
    (mp_tac (Q.INST [`op` |-> `FST (FST (coords:(operand # operand) # (operand # operand)))`,
      `w` |-> `n2w j:bytes32`, `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`,
      `next` |-> `prepared.cs_next_var`, `d` |-> `d+32`, `sz` |-> `output_size-32`,
      `lo` |-> `prepared.cs_next_id`, `hi` |-> `end_st.cs_next_id`] abi_scratch_effect_operand) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `child_ids` |-> `abi_decoder_ids prepared.cs_next_id end_st.cs_next_id`,
    `fp` |-> `[(d+32+j*asz,LENGTH (enc ty (EL j avs)))]`,
    `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_frame_subset_append) >>
  impl_tac >- (gvs[APPEND, Excl "enc_def"] >> simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >> disch_tac >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `next` |-> `st.cs_next_var`,
    `fp` |-> `[(d+32+j*asz,LENGTH (enc ty (EL j avs)))]`] abi_scratch_frame_after_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`child_lo` |-> `prepared.cs_next_id`, `child_hi` |-> `end_st.cs_next_id`,
    `child_next` |-> `prepared.cs_next_var`, `child_d` |-> `d+32`, `child_sz` |-> `output_size-32`,
    `lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_scratch_effect_after_address) >>
  impl_tac >- (asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >> disch_tac >>
  qexists_tac `actual` >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED

(* The actual static-element body advances complete source/output observations.
   TOP-LEVEL: abi_scratch_array_static_body_memory retains the registered index
   and complete source contract at the loop's stable compiler entry. *)
Theorem abi_scratch_array_static_body_memory:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st j actual /\ eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  `owner_st.cs_next_id <= last /\ first <= st.cs_next_id /\ site < last /\ site < st.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `off` |-> `j:num`,
    `s` |-> `initial:venom_state`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial` by
    (irule abi_scratch_input_mono >> qexists_tac `owner_st` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`p` |-> `n2w slot:bytes32`] abi_scratch_array_static_body_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_scratch_array_static_bounds >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ owner_st _ _ _ _ _ _ _ _ _ _ initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  qpat_assum `asz = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`]
    abi_scratch_array_static_step) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `active` |-> `T`, `off` |-> `j:num`,
    `owned_lo` |-> `st.cs_next_id`, `owned_hi` |-> `end_st.cs_next_id`, `next` |-> `owner_st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_scratch_cursor_protected) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei (abi_member_head_size ty) msz F`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `st` |-> `owner_st`, `lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `owner_st.cs_next_var`, `sz` |-> `output_size:num`] abi_scratch_input_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Actual static-body/backedge execution advances complete array observations.
   TOP-LEVEL: abi_scratch_array_static_round combines the generated child body
   with the real index update. Helper: backedge preservation of complete buffers. *)
Theorem abi_scratch_array_static_backedge_memory:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs k d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  owner_st.cs_next_var <= next /\ owner_st.cs_next_id <= last /\ abi_decoder_budget first last b cap initial ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs k d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_scratch_effect first last site (site+1) next limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `site < last /\ site+1 <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `off` |-> `j:num`,
    `s` |-> `initial:venom_state`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_operand_live next ip` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`lo` |-> `site:num`, `hi` |-> `site+1`, `sz` |-> `output_size:num`]
    abi_scratch_array_backedge) >> impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(slot,32)]` >>
     asm_simp_tac (srw_ss()) [] >> qexistsl_tac [`slot`, `32`] >> simp[] >>
     irule abi_scratch_registered_member >> simp[] >> qexists_tac `site` >> simp[abi_decoder_ids_def]) >>
  `has_type (Array NONE ty) (ListV avs)` by
    (qpat_assum `abi_encoder_input (AbiDynArray _ _ _ _) _ _ _ _ _`
       (ACCEPT_TAC o MATCH_MP abi_encoder_input_typed)) >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`,
    `j` |-> `k:num`] abi_encoder_array_prefix_output_frame) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz F`, `at` |-> `Array NONE ty`, `av` |-> `ListV avs`,
    `st` |-> `owner_st`, `lo` |-> `site:num`, `hi` |-> `site+1`, `sz` |-> `output_size:num`]
    abi_scratch_input_effect) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `active` |-> `T`,
    `off` |-> `j:num`, `next_off` |-> `SUC j`, `owned_lo` |-> `site:num`, `owned_hi` |-> `site+1`,
    `sz` |-> `output_size:num`] abi_scratch_cursor_registered) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_array_static_round:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\ lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = end_st.cs_current_insts ++ abi_decode_backedge_insts end_st.cs_next_id
    (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString end_st.cs_next_var)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id+3 <= last /\
  end_st.cs_next_var+1 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  drule abi_encode_array_static_body_index >> disch_tac >>
  `owner_st.cs_next_id <= last /\ end_st.cs_next_id <= last /\
   end_st.cs_next_var <= limit_st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var /\
   owner_st.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  mp_tac abi_scratch_array_static_body_memory >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial encoded` >>
  qpat_assum `out = Var _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encoder_input_typed >> disch_tac >>
  `j <= LENGTH avs` by decide_tac >> drule_all abi_encoder_array_prefix_types >> strip_tac >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  mp_tac (Q.INST [`initial` |-> `encoded:venom_state`, `k` |-> `SUC j`, `n` |-> `LENGTH (avs:abi_value list)`,
    `prefix` |-> `end_st.cs_current_insts`, `id` |-> `end_st.cs_next_id`, `next` |-> `end_st.cs_next_var`,
    `iv` |-> `STRING #"%" (toString st.cs_next_var)`] abi_scratch_array_static_backedge_memory) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  `first <= site /\ site <= st.cs_next_id` by (fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial encoded` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `site+1`, `site`, `end_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `encoded` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED

(* Finite execution of actual static-element array iterations with physical frames.
   TOP-LEVEL: abi_scratch_array_static_finite_loop reaches the real exit edge.
   Helper: the actual header/body/backedge preserves the complete loop invariant. *)
Theorem abi_scratch_array_loop_static_step:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual. abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`active` |-> `F`] abi_scratch_array_loop_header) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `j < LENGTH avs` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, COND_CLAUSES]) >> assume_tac th) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_assum `abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST (SND labels)) j origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  drule abi_encoder_array_loop_header_phi >> disch_then (qx_choose_then `hdr_bb` strip_assume_tac) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb func.fn_blocks = SOME back_bb` >>
  `owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
    body_end.cs_next_id+3 <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `body_st`, `end_st` |-> `body_end`, `out` |-> `idx`, `initial` |-> `ready:venom_state`,
    `lo` |-> `site:num`, `hdr` |-> `FST (labels:string # string # string)`, `bb` |-> `back_bb`]
    abi_scratch_array_static_round) >>
  impl_tac >- full_simp_tac (srw_ss()) [Abbr`back_bb`, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `body_end.cs_next_id+3`, `site`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.INST [`active` |-> `F`, `initial` |-> `ready:venom_state`, `k` |-> `SUC j`,
    `label` |-> `FST (SND (labels:string # string # string))`,
    `next_label` |-> `FST (labels:string # string # string)`] abi_scratch_array_loop_inv_advance) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_cursor_def] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED

Theorem abi_scratch_array_static_finite_loop:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual. abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
      (SND (SND labels)) (LENGTH avs) origin actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `i <= LENGTH avs` by (drule abi_scratch_array_loop_inv_facts >> simp[]) >>
  qabbrev_tac `loop_inv = \(j:num) (s:venom_state).
    abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin s` >>
  qabbrev_tac `loop_post = \(s:venom_state).
    abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (SND (SND labels)) (LENGTH avs) origin s` >>
  mp_tac (Q.SPECL [`LENGTH (avs:abi_value list)`, `i:num`, `loop_inv`, `loop_post`, `ctx`, `func`, `initial:venom_state`]
    abi_decode_finite_iteration) >>
  impl_tac
  >- (asm_simp_tac bool_ss [Abbr`loop_inv`, Abbr`loop_post`] >> conj_tac
      >- (qx_genl_tac [`j`, `u`] >> strip_tac >>
          mp_tac (Q.INST [`j` |-> `j:num`, `initial` |-> `u:venom_state`] abi_scratch_array_loop_static_step) >>
          impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
      qx_gen_tac `u` >> strip_tac >>
      mp_tac (Q.INST [`active` |-> `F`, `initial` |-> `u:venom_state`] abi_scratch_array_loop_exit) >>
      impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [Abbr`loop_post`]
QED

(* ===== Run ===== *)

(* Compose the actual entry, finite static iterations and count-reload exit.
   TOP-LEVEL: abi_scratch_array_static_loop_run returns exact ABI bytes/length
   and the physical effect from the original loop state. *)

Theorem abi_scratch_array_static_loop_result:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_exit src asz exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_array_static_finite_loop >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_var <= exit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`initial` |-> `prepared:venom_state`, `label` |-> `SND (SND (labels:string # string # string))`,
    `st` |-> `exit_st`] abi_scratch_array_static_scalar_exit) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]
QED

Theorem abi_scratch_array_static_loop_run:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_exit src asz exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_decoder_operand_live owner_st.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\ initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
  ~initial.vs_halted ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `cursor_site` |-> `0:num`,
    `cursor_slot` |-> `0:num`] abi_scratch_array_loop_enter) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_cursor_def] >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `0:num`, `origin` |-> `initial:venom_state`, `dyn_ptr` |-> `Lit 0w`,
    `cursor_site` |-> `0:num`, `cursor_slot` |-> `0:num`,
    `initial` |-> `jump_to (FST (labels:string # string # string)) initial`]
    abi_scratch_array_static_loop_result) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >>
  qexists_tac `jump_to (FST (labels:string # string # string)) initial` >> simp[]
QED

(* ===== Scratch Array Static Loop ===== *)

(* The actual full static-element loop preserves complete physical resources.
   TOP-LEVEL: abi_scratch_array_static_loop composes real index initialization,
   entry, all static child/backedge iterations and the exact count-reload exit. *)

Theorem abi_scratch_array_static_loop:
  abi_encoder_static_leaf ei /\
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_id <= hi /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var` by
    (qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `st'` |-> `owner_st`, `index_ptr` |-> `ip:operand`, `active` |-> `F`]
    abi_scratch_array_index_prepare) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  rename1 `abi_encoder_cursor T ip start.cs_next_id slot first start.cs_next_id owner_st 0 ready` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (qpat_assum `!op w. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`site` |-> `start.cs_next_id`, `initial` |-> `ready:venom_state`]
    abi_scratch_array_static_loop_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `owner_st.cs_next_id`, `start.cs_next_id`, `start.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `start.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED
