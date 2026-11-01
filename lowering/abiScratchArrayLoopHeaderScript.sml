(* The real header transports the precise invariant onto its selected edge.
   TOP-LEVEL: abi_scratch_array_loop_header retains complete source buffers,
   both cursors and the accumulated physical effect on body and exit edges. *)
Theory abiScratchArrayLoopHeader
Ancestors
  abiScratchArrayLoopInvariant abiScratchArrayHeader abiScratchAddress abiScratchInput
  abiScratchEncoderContract abiEncoderArrayLoopCode abiEncoderMembersDefs abiEncoderArrayPrefix
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderLoop abiDecoderContract compileEnv
  venomState venomInst venomExecSemantics valueEncoding contractABI words list arithmetic

Theorem abi_scratch_array_loop_header:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial ==>
  ?ready. abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
      (if j < LENGTH avs then FST (SND labels) else SND (SND labels)) j origin ready /\
    abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
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
    `exit_lbl` |-> `SND (SND (labels:string # string # string))`] abi_scratch_array_header) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `abi_encoder_cursor T ip site slot first site owner_st j ready /\
   abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
     (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) ready` by
    (conj_tac >> qpat_assum `!act op cursor_site cursor_slot cursor_lo off. _` irule >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`, `lo` |-> `site:num`,
    `next` |-> `owner_st.cs_next_var`, `sz` |-> `output_size:num`] abi_scratch_address_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`, `av` |-> `ListV avs`,
    `st` |-> `owner_st`, `lo` |-> `site:num`, `next` |-> `owner_st.cs_next_var`,
    `sz` |-> `output_size:num`, `actual` |-> `ready:venom_state`] abi_scratch_input_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`k` |-> `j:num`, `label` |-> `FST (labels:string # string # string)`,
    `next_label` |-> `if j < LENGTH (avs:abi_value list) then FST (SND (labels:string # string # string))
      else SND (SND (labels:string # string # string))`, `actual` |-> `ready:venom_state`]
    abi_scratch_array_loop_inv_advance) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED
