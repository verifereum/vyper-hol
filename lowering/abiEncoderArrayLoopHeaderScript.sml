(* The actual header transports the finite-loop invariant to its selected edge. *)
Theory abiEncoderArrayLoopHeader
Ancestors
  abiEncoderArrayLoopCode abiEncoderArrayLoopInvariant abiEncoderArrayHeaderMemory abiEncoderArrayHeader
  abiEncoderArrayMemory abiEncoderMembersDefs abiDecoderEffect abiDecoderContract abiDecoderLoop
  fragExec compileEnv venomState venomInst venomExecSemantics valueEncoding contractABI words list arithmetic

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
