Theory abiEncoderArrayLoopDynamicStep
Ancestors
  abiEncoderArrayLoopCode abiEncoderArrayLoopInvariant abiEncoderArrayHeaderMemory
  abiEncoderArrayHeader abiEncoderArrayMemory abiEncoderMembersDefs abiDecoderEffect
  abiDecoderContract abiDecoderLoop fragExec compileEnv venomState venomInst venomExecSemantics
  valueEncoding contractABI words list arithmetic abiEncoderChildInputs
  abiDecoderPrimitiveLoopEntry abiDecoderRecursiveLoopEntry abiDecoderLoopRegisters
  abiDecoderReentry abiEncoderArrayRound abiEncoderArrayCode abiEncoderAdmissible
  abiEncoderArrayDynamicRound abiEncoderCorrect

(* The actual header transports the finite-loop invariant to its selected edge. *)
Theorem abi_encoder_array_loop_header_phi:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels ==>
  ?hdr_bb. lookup_block (FST labels) func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0
Proof
  simp_tac bool_ss [abi_encoder_array_loop_code_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `lookup_block (FST labels) func.fn_blocks = SOME header_bb` >>
  qexists_tac `header_bb` >> asm_simp_tac bool_ss [] >>
  simp[Abbr`header_bb`, abi_encode_array_header_insts_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_encoder_array_loop_header:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial ==>
  ?ready. abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
      (if j < LENGTH avs then FST (SND labels) else SND (SND labels)) j origin ready /\
    abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_inv_def]) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  qpat_x_assum `?bb. lookup_block body_st.cs_current_bb _ = _ /\ _`
    (qx_choose_then `body_bb` strip_assume_tac) >>
  qpat_x_assum `?bb. lookup_block exit_st.cs_current_bb _ = _ /\ _`
    (qx_choose_then `exit_bb` strip_assume_tac) >>
  qpat_assum `body_st.cs_current_bb = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qpat_assum `exit_st.cs_current_bb = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_var+3 <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `k` |-> `j:num`, `lo` |-> `site:num`,
    `id` |-> `owner_st.cs_next_id+1`, `hdr` |-> `FST (labels:string # string # string)`,
    `body_lbl` |-> `FST (SND (labels:string # string # string))`,
    `exit_lbl` |-> `SND (SND (labels:string # string # string))`,
    `off` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j (avs:abi_value list)))`] abi_encoder_array_header_memory) >>
  impl_tac >- full_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`k` |-> `j:num`, `label` |-> `FST (labels:string # string # string)`,
    `next_label` |-> `if j < LENGTH (avs:abi_value list) then FST (SND (labels:string # string # string))
      else SND (SND (labels:string # string # string))`, `actual` |-> `ready:venom_state`]
    abi_encoder_array_loop_inv_advance) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

(* Execute the real initial JMP and establish the finite encoder invariant at index zero. *)
Theorem abi_encoder_array_memory_jump[simp]:
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j
    (jump_to hdr s) <=>
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j s
Proof
  simp[abi_encoder_array_memory_def, abi_encoder_buffer_pre_def, jump_to_def]
QED

Theorem abi_encoder_cursor_jump[simp]:
  abi_encoder_cursor active cursor_op site slot first lo st off (jump_to hdr s) <=>
  abi_encoder_cursor active cursor_op site slot first lo st off s
Proof
  simp[abi_encoder_cursor_def, abi_decoder_operand_jump, jump_to_def, mload_def]
QED

Theorem abi_encoder_array_loop_entry_sim:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  abi_decode_sim ctx func initial (jump_to (FST labels) initial)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_loop_header_phi >> strip_tac >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `fn` |-> `func:ir_function`,
    `prefix` |-> `owner_st.cs_current_insts`, `id` |-> `owner_st.cs_next_id`,
    `hdr` |-> `FST (labels:string # string # string)`,
    `bb` |-> `<|bb_label := owner_st.cs_current_bb; bb_instructions := owner_st.cs_current_insts ++
      [mk_inst owner_st.cs_next_id JMP [Label (FST (labels:string # string # string))] []]|>`]
    abi_decoder_loop_entry_sim) >>
  impl_tac >- gvs[] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_loop_enter:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap 0 initial /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
    (FST labels) 0 initial (jump_to (FST labels) initial) /\
  abi_decode_sim ctx func initial (jump_to (FST labels) initial)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial
    (jump_to (FST labels) initial)` by
    (irule abi_decoder_effect_jump >> asm_simp_tac bool_ss []) >>
  drule_all abi_encoder_array_loop_entry_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  asm_simp_tac (srw_ss()) [abi_encoder_array_loop_inv_def, jump_to_def,
    abi_encoder_array_memory_jump, abi_encoder_cursor_jump, abi_decoder_operand_jump]
QED

(* One actual header/static-body/backedge iteration preserves the finite-loop invariant. *)
Theorem abi_encoder_array_loop_static_step:
  abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual. abi_encoder_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`active` |-> `F`] abi_encoder_array_loop_header) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `j < LENGTH avs` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, COND_CLAUSES]) >> assume_tac th) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_assum `abi_encoder_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST (SND labels)) j origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_inv_def]) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  drule abi_encoder_array_loop_header_phi >> disch_then (qx_choose_then `hdr_bb` strip_assume_tac) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb func.fn_blocks = SOME back_bb` >>
  `owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
    body_end.cs_next_id+3 <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `body_st`, `end_st` |-> `body_end`, `out` |-> `idx`, `initial` |-> `ready:venom_state`,
    `lo` |-> `site:num`, `hdr` |-> `FST (labels:string # string # string)`, `bb` |-> `back_bb`]
    abi_encoder_array_static_round) >>
  impl_tac >- full_simp_tac (srw_ss()) [Abbr`back_bb`, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `body_end.cs_next_id+3`, `site`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.INST [`active` |-> `F`, `initial` |-> `ready:venom_state`, `k` |-> `SUC j`,
    `label` |-> `FST (SND (labels:string # string # string))`,
    `next_label` |-> `FST (labels:string # string # string)`] abi_encoder_array_loop_inv_advance) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_cursor_def] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

(* One actual header/dynamic-body/backedge iteration preserves the finite-loop invariant. *)
Theorem abi_encoder_array_loop_dynamic_step:
  abi_encoder_correct ei /\
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual. abi_encoder_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`active` |-> `T`] abi_encoder_array_loop_header) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `j < LENGTH avs` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, COND_CLAUSES]) >> assume_tac th) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_assum `abi_encoder_array_loop_inv ei asz msz T ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST (SND labels)) j origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_inv_def]) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  drule abi_encoder_array_loop_header_phi >> disch_then (qx_choose_then `hdr_bb` strip_assume_tac) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb func.fn_blocks = SOME back_bb` >>
  `owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
    body_end.cs_next_id+3 <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `body_st`, `end_st` |-> `body_end`, `out` |-> `idx`, `initial` |-> `ready:venom_state`,
    `lo` |-> `site:num`, `hdr` |-> `FST (labels:string # string # string)`, `bb` |-> `back_bb`]
    abi_encoder_array_dynamic_round) >>
  impl_tac >- full_simp_tac (srw_ss()) [Abbr`back_bb`, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `body_end.cs_next_id+3`, `site`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.INST [`active` |-> `T`, `initial` |-> `ready:venom_state`, `k` |-> `SUC j`,
    `label` |-> `FST (SND (labels:string # string # string))`,
    `next_label` |-> `FST (labels:string # string # string)`] abi_encoder_array_loop_inv_advance) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_cursor_def] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED
