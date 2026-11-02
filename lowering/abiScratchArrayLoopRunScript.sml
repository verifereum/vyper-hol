Theory abiScratchArrayLoopRun
Ancestors
  abiScratchArrayLoopInvariant abiScratchAddress abiScratchEncoderContract
  abiEncoderArrayLoopDynamicStep abiEncoderArrayLoopCode abiEncoderMembersDefs
  abiDecoderDynamicLoopSetup abiDecoderLoopRegisters abiDecoderFootprint abiDecoderLoop
  abiDecoderReentry compileEnv valueEncoding contractABI venomState venomExecSemantics words
  list arithmetic abiScratchEffect abiEncoderArrayExit abiEncoderArrayHeaderMemory
  abiEncoderArrayBodyCode abiEncoderArrayPrefix abiEncoderInput abiDecodeRanges
  abiDecoderContract abiScratchArrayFiniteLoop

(* Execute the real initial JMP and establish the precise finite-loop invariant.
   TOP-LEVEL: abi_scratch_array_loop_enter starts at index zero without changing
   the source, output, cursor observations or physical scratch footprint. *)
Theorem abi_scratch_input_jump[simp]:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap (jump_to hdr s) <=>
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap s
Proof
  simp[abi_scratch_input_def, abi_decoder_operand_jump, jump_to_def, abi_decoder_child_scratch_def]
QED

Theorem abi_scratch_effect_jump:
  abi_decoder_budget first last b cap initial /\ fresh_vars_wrt limit_st initial ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial (jump_to hdr initial)
Proof
  strip_tac >> irule abi_scratch_address_effect >>
  simp[abi_decoder_address_frame_def, abi_decoder_operand_jump, jump_to_def, abi_decoder_fresh_jump]
QED

Theorem abi_scratch_array_loop_enter:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
    (FST labels) 0 initial (jump_to (FST labels) initial) /\
  abi_decode_sim ctx func initial (jump_to (FST labels) initial)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial
    (jump_to (FST labels) initial)` by
    (irule abi_scratch_effect_jump >> asm_simp_tac bool_ss []) >>
  drule_all abi_encoder_array_loop_entry_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  asm_simp_tac (srw_ss()) [abi_scratch_array_loop_inv_def, jump_to_def,
    abi_scratch_input_jump, abi_encoder_cursor_jump, abi_decoder_operand_jump]
QED

(* Read the actual exit length after the precise invariant reaches the last index.
   TOP-LEVEL: abi_scratch_array_dynamic_scalar_exit returns the complete ABI
   bytes and length with a composed physical effect from the loop origin.
   Helper: the completed prefix identifies the final tail cursor exactly. *)
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

(* The real entry jump, finite dynamic iterations and scalar exit form one run.
   TOP-LEVEL: abi_scratch_array_dynamic_loop_run returns exact ABI bytes and
   length while composing its physical effect from the original loop state. *)
Theorem abi_scratch_array_dynamic_loop_result:
  abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_dynamic_exit src dyn_ptr exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_array_dynamic_finite_loop >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_var <= exit_st.cs_next_var /\ owner_st.cs_next_id <= last` by decide_tac >>
  mp_tac (Q.INST [`initial` |-> `prepared:venom_state`, `label` |-> `SND (SND (labels:string # string # string))`,
    `st` |-> `exit_st`] abi_scratch_array_dynamic_scalar_exit) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]
QED

Theorem abi_scratch_array_dynamic_loop_run:
  abi_scratch_encoder ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_dynamic_exit src dyn_ptr exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  site < cursor_site /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
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
  mp_tac (Q.INST [`active` |-> `T`] abi_scratch_array_loop_enter) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `0:num`, `origin` |-> `initial:venom_state`,
    `initial` |-> `jump_to (FST (labels:string # string # string)) initial`]
    abi_scratch_array_dynamic_loop_result) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >>
  qexists_tac `jump_to (FST (labels:string # string # string)) initial` >> simp[]
QED
