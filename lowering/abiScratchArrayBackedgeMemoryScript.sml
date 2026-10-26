(* The actual backedge retains complete buffers and the advanced tail cursor.
   TOP-LEVEL: abi_scratch_array_backedge_memory increments the index while
   preserving any processed output prefix and the enclosing source contract. *)
Theory abiScratchArrayBackedgeMemory
Ancestors
  abiScratchArrayBackedge abiScratchInputEffect abiScratchCursor abiScratchFootprint
  abiScratchEncoderContract abiEncoderArrayCursor abiEncoderArrayFrame abiEncoderArrayPrefix
  abiEncoderMembersDefs abiEncoderInput abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderLoop abiDecoderArrayBackedge abiDecoderReentry compileEnv
  valueEncodingProps valueEncoding contractABI venomState venomInst finite_map words list arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_BACKEDGE_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch backedge memory not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayBackedgeMemory");
