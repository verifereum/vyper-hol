Theory abiEncoderArrayBackedge
Ancestors
  abiEncoderArrayFrame abiEncoderChildEffect abiEncoderChildFrames abiDecoderExecution
  abiDecoderLoopRegisters abiDecoderArrayBackedge abiDecoderIndexInit abiDecoderArrayInitExec
  abiDecoderEffect abiDecoderAllocation abiDecoderProtectedScratch abiDecoderReentry
  abiDecoderFrame abiDecoderContract emitHelperProps exprLoweringProps compileEnv venomState
  venomExecSemantics words list finite_map pred_set arithmetic abiEncoderArrayIndex
  abiEncoderArrayMemory abiEncoderArrayCursor abiEncoderMembersDefs abiEncoderChildInputs
  abiDecoderLoop valueEncoding contractABI

(* ===== Encoder Array Backedge ===== *)

(* Execute the shared ADD/MSTORE/JMP backedge and own its registered index slot.
   TOP-LEVEL: concrete execution and a reusable single-scratch-write effect. *)

Theorem abi_encoder_array_backedge_execute:
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. exec_block fuel ctx bb s = OK actual /\
    mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s) /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] s actual /\
    actual = jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString next)) (n2w (SUC j)) s))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `ip <> Var (STRING #"%" (toString next))` by
    (mp_tac (Q.INST [`first` |-> `next:num`, `op` |-> `ip:operand`] abi_decoder_live_excludes_output) >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  qabbrev_tac `actual = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString next)) (n2w (SUC j)) s))` >>
  `exec_block fuel ctx bb s = OK actual` by
    (drule_all abi_decode_backedge_control >> simp[Abbr`actual`, w2n_n2w]) >>
  `abi_decode_footprint_frame [(slot,32)] s actual /\ mload slot actual = n2w (SUC j)` by
    (mp_tac (Q.INST [`p` |-> `n2w slot:bytes32`, `fp` |-> `[(slot:num,32:num)]`,
      `nv` |-> `STRING #"%" (toString (next:num))`, `w` |-> `n2w (SUC j):bytes32`]
      (INST_TYPE [alpha |-> ``:256``] abi_decode_backedge_observations)) >>
     simp[Abbr`actual`, w2n_n2w]) >>
  `fresh_vars_wrt limit_st actual` by
    simp[Abbr`actual`, abi_decoder_generated_update_fresh, fresh_vars_wrt_mstore] >>
  `!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s` by
    (rpt strip_tac >> asm_simp_tac bool_ss [Abbr`actual`, abi_decoder_operand_jump,
      abi_decoder_operand_mstore, abi_decoder_generated_update_operand]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  simp[Abbr`actual`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_array_backedge_reach:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s) /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] s actual /\ abi_decode_sim ctx func s actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`fuel` |-> `0:num`] abi_encoder_array_backedge_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `ip <> Var (STRING #"%" (toString next))` by
    (mp_tac (Q.INST [`first` |-> `next:num`, `op` |-> `ip:operand`] abi_decoder_live_excludes_output) >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  mp_tac (Q.INST [`fn` |-> `func`, `nv` |-> `STRING #"%" (toString (next:num))`,
    `p` |-> `n2w slot:bytes32`, `i` |-> `j:num`, `ncount` |-> `n:num`] abi_decode_backedge_sim) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac (srw_ss()) [w2n_n2w] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_single_scratch_effect:
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
  actual.vs_halted = initial.vs_halted /\ fresh_vars_wrt limit_st actual /\
  (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op initial) /\
  abi_decode_footprint_frame [(slot,32)] initial actual /\ (d+sz <= b \/ b+cap <= d) ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `abi_decode_footprint_frame [(d,sz);(slot,32)] initial actual` by
    (irule abi_encoder_frame_extra_window >> asm_simp_tac bool_ss []) >>
  drule_all abi_encoder_owned_scratch_frame >> disch_tac >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(slot,32)]` >>
     asm_simp_tac (srw_ss()) [] >> qexistsl_tac [`b`, `cap`] >> asm_simp_tac (srw_ss()) []) >>
  asm_simp_tac bool_ss [abi_decoder_effect_def]
QED

(* ===== Memory ===== *)

(* The actual backedge advances the index and preserves the encoded prefix and tail cursor. *)

Theorem abi_encoder_array_backedge_memory:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\
  abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap k initial /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo owner_st off initial /\
  (active ==> site < cursor_site) /\ owner_st.cs_next_id <= last /\
  owner_st.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  j < LENGTH avs /\ fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial ==>
  ?actual. abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap
      d output_size b cap k actual /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo owner_st off actual /\
    abi_decoder_effect first last site (site+1) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_memory_typed >> strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `s` |-> `initial:venom_state`,
    `cursor_op` |-> `ip:operand`, `off` |-> `j:num`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_operand_live next ip` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `n` |-> `LENGTH (avs:abi_value list)`]
    abi_encoder_array_backedge_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`lo` |-> `site:num`, `hi` |-> `site+1`, `sz` |-> `output_size:num`]
    abi_encoder_single_scratch_effect) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> disch_tac >>
  `abi_decoder_effect first last site (site+1) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >> qexistsl_tac [`d`, `site+1`, `site`, `next`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `new_j` |-> `SUC j`] abi_encoder_array_index_update) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
