Theory abiScratchArrayBackedge
Ancestors
  abiScratchEncoderContract abiScratchEffect abiEncoderArrayBackedge abiDecoderAllocation
  abiDecoderArrayBackedge abiDecoderFootprint abiDecoderLoop abiDecoderReentry compileEnv
  venomState venomInst words finite_map list arithmetic abiScratchInput abiScratchCursor
  abiScratchFootprint abiEncoderArrayCursor abiEncoderArrayFrame abiEncoderArrayPrefix
  abiEncoderMembersDefs abiEncoderInput abiDecoderFrame valueEncodingProps valueEncoding
  contractABI

(* ===== Scratch Array Backedge ===== *)

(* Execute the actual ADD/MSTORE/JMP backedge with physical scratch ownership.
   TOP-LEVEL: abi_scratch_array_backedge reuses concrete CFG execution and
   charges the index update to its registered allocation site. *)

Theorem abi_scratch_array_backedge:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\ eval_operand ip initial = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
  ?actual. mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op initial) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`] abi_encoder_array_backedge_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac abi_scratch_single_write >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* ===== Memory ===== *)

(* The actual backedge retains complete buffers and the advanced tail cursor.
   TOP-LEVEL: abi_scratch_array_backedge_memory increments the index while
   preserving any processed output prefix and the enclosing source contract. *)

Theorem abi_scratch_array_backedge_memory:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs k d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first lo owner_st off initial /\
  site < cursor_site /\ owner_st.cs_next_var <= next /\ owner_st.cs_next_id <= last /\
  abi_decoder_budget first last b cap initial ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs k d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first lo owner_st off actual /\
    abi_scratch_effect first last site (site+1) next limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_encoder_cursor T dyn_ptr _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `site < last /\ cursor_site < last /\ site+1 <= last` by decide_tac >>
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
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz T`, `at` |-> `Array NONE ty`, `av` |-> `ListV avs`,
    `st` |-> `owner_st`, `lo` |-> `site:num`, `hi` |-> `site+1`, `sz` |-> `output_size:num`]
    abi_scratch_input_effect) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `active` |-> `T`,
    `off` |-> `j:num`, `next_off` |-> `SUC j`, `owned_lo` |-> `site:num`, `owned_hi` |-> `site+1`,
    `sz` |-> `output_size:num`] abi_scratch_cursor_registered) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `dyn_ptr:operand`, `active` |-> `T`,
    `site` |-> `cursor_site:num`, `slot` |-> `cursor_slot:num`, `owned_lo` |-> `site:num`,
    `owned_hi` |-> `site+1`, `sz` |-> `output_size:num`] abi_scratch_cursor_protected) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
