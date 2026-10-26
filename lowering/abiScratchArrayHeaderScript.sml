(* Actual encoder-header execution with precise scratch ownership.
   TOP-LEVEL: abi_scratch_array_header preserves complete source/output data
   and all live cursors on both the body and exit edges. *)
Theory abiScratchArrayHeader
Ancestors
  abiScratchAddress abiScratchFootprint abiEncoderArrayHeader abiEncoderArrayHeaderFrame
  abiEncoderArrayCursor abiEncoderArrayLayout abiEncoderMembersDefs abiEncoderInput
  abiEncoderArrayPrefix abiDecoderDynamicLoopSetup abiDecoderLoopRegisters abiDecoderArrayBackedge
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  abiDecoderLoop abiDecoderContract compileEnv valueEncoding contractABI
  venomState venomExecSemantics venomInst words list arithmetic

Theorem abi_scratch_array_header:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op (STRING #"%" (toString st.cs_next_var))
      (STRING #"%" (toString (st.cs_next_var+1))) (STRING #"%" (toString (st.cs_next_var+2)))
      body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  initial.vs_current_bb = hdr /\ initial.vs_inst_idx = 0 /\ ~initial.vs_halted /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  abi_encoder_array_prefix ty avs k d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo st j initial /\ j <= LENGTH avs /\
  abi_decoder_operand_live st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  st.cs_next_id <= last /\ st.cs_next_var+3 <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial ==>
  ?actual.
    abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs k d actual.vs_memory /\
    (!act op cursor_site cursor_slot cursor_lo off.
      abi_encoder_cursor act op cursor_site cursor_slot first cursor_lo st off initial ==>
      abi_encoder_cursor act op cursor_site cursor_slot first cursor_lo st off actual) /\
    eval_operand count_op actual = SOME (n2w (LENGTH avs)) /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual =
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial /\
    actual.vs_current_bb = (if j < LENGTH avs then body_lbl else exit_lbl) /\
    actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule abi_encoder_input_typed >> strip_tac >>
  drule_all abi_encoder_array_prefix_types >> strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`cursor_op` |-> `ip:operand`, `off` |-> `j:num`, `s` |-> `initial:venom_state`]
    abi_encoder_cursor_bounds) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `count_op <> Var (STRING #"%" (toString st.cs_next_var))` by
    (mp_tac (Q.INST [`first` |-> `st.cs_next_var`, `next` |-> `st.cs_next_var`,
       `op` |-> `count_op:operand`] abi_decoder_live_excludes_output) >> simp[]) >>
  qabbrev_tac `actual = jump_to (if j < LENGTH avs then body_lbl else exit_lbl)
    (abi_encode_array_header_state (STRING #"%" (toString st.cs_next_var))
      (STRING #"%" (toString (st.cs_next_var+1))) (STRING #"%" (toString (st.cs_next_var+2)))
      j (LENGTH avs) initial)` >>
  `abi_decoder_address_frame st.cs_next_var initial actual` by
    simp[Abbr`actual`, abi_encode_array_header_address_frame] >>
  `!act op cursor_site cursor_slot cursor_lo off.
    abi_encoder_cursor act op cursor_site cursor_slot first cursor_lo st off initial ==>
    abi_encoder_cursor act op cursor_site cursor_slot first cursor_lo st off actual` by
    (rpt gen_tac >> strip_tac >>
     drule_all (SIMP_RULE bool_ss [LESS_EQ_REFL]
       (Q.INST [`prepared` |-> `st:compile_state`] abi_encoder_cursor_address)) >> simp[]) >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `fp` |-> `abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`,
    `next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`]
    abi_scratch_address) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `n` |-> `LENGTH (avs:abi_value list)`,
    `i` |-> `j:num`, `p` |-> `n2w slot:bytes32`, `iv` |-> `STRING #"%" (toString st.cs_next_var)`,
    `cmp` |-> `STRING #"%" (toString (st.cs_next_var+1))`,
    `done` |-> `STRING #"%" (toString (st.cs_next_var+2))`] abi_encode_array_header_sim) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w] >> disch_tac >>
  `fresh_vars_wrt limit_st actual` by
    (simp_tac bool_ss [Abbr`actual`, abi_decoder_fresh_jump] >>
     irule abi_encode_array_header_registers >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  fs[abi_decoder_address_frame_def] >>
  simp[Abbr`actual`, jump_to_def, abi_encode_array_header_state_def, update_var_def] >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_HEADER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch array header not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayHeader");
