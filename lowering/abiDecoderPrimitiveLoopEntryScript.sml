(* Connect the compiled loop's initial JMP to its checked finite execution. *)
Theory abiDecoderPrimitiveLoopEntry
Ancestors
  abiDecoderPrimitiveDynLoop abiDecoderPrimitiveLoopLayout abiDecoderLoopEmit
  abiDecoderPrimitiveLoopFragment abiDecoderPrimitiveLoopContext
  abiDecoderPrimitiveLoopInvariant abiDecoderPrimitiveLoopFinite
  abiDecoderArrayInvariant abiDecoderLoopRegisters abiDecoderExecution abiDecoderLoop
  abiDecoderContract abiDecoderFrame fragExec exprLoweringProps emitHelperProps
  compileEnv venomExecSemantics venomState venomInst words list arithmetic

Theorem abi_decoder_loop_entry_code:
  compile_abi_decode_dyn_loop dst src opc hi (DecPrimWord clamp) 32 32 ip cnt
    start = ((),end_st) /\ fn_has_code start end_st fn /\ abi_decode_source_opcode opc ==>
  ?bb hdr_bb.
    lookup_block start.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = start.cs_current_insts ++
      [mk_inst start.cs_next_id JMP
        [Label (fresh_label_output "dec_dyn_hdr" start.cs_next_label)] []] /\
    lookup_block (fresh_label_output "dec_dyn_hdr" start.cs_next_label) fn.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0
Proof
  strip_tac >> drule_all abi_decode_dyn_loop_trace >> strip_tac >>
  `st0.cs_current_insts = []` by
    gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def] >>
  drule_all abi_decoder_primitive_setup_head >> strip_tac >>
  drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >>
  gvs[abi_decode_loop_prefix_state_def, abi_decode_loop_suffix_state_def,
      fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decoder_loop_entry_control:
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  exec_block fuel ctx bb s = OK (jump_to hdr s)
Proof
  strip_tac >>
  simp[Once exec_block_def, get_instruction_def, EL_APPEND_EQN] >>
  simp[step_inst_def, Once step_inst_base_def, mk_inst_def, is_terminator_def, jump_to_def]
QED

Theorem abi_decoder_loop_entry_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  abi_decode_sim ctx fn s (jump_to hdr s)
Proof
  strip_tac >> irule abi_decode_edge_sim >> simp[jump_to_def] >>
  gen_tac >> drule_all abi_decoder_loop_entry_control >> simp[jump_to_def]
QED

Theorem abi_decoder_loop_rel_jump:
  fresh_vars_wrt limit_st s ==>
  abi_decoder_loop_rel first limit_st fp s (jump_to hdr s)
Proof
  simp[abi_decoder_loop_rel_def, abi_decode_footprint_frame_refl, jump_to_def,
       fresh_vars_wrt_def, abi_decode_footprint_frame_def, eval_operand_def, lookup_var_def]
QED

Theorem abi_decoder_primitive_dyn_loop:
  compile_abi_decode_dyn_loop dst src opc hi (DecPrimWord clamp) 32 32 ip cnt
    start = ((),end_st) /\ fn_has_code start end_st fn /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs start.cs_next_var ip src dst sb d slot initial /\
  abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 initial /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\ mload slot initial = 0w /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_decoder_loop_rel start.cs_next_var limit_st fp initial t /\
    t.vs_current_bb = fresh_label_output "dec_dyn_exit" (start.cs_next_label + 2) /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\ mload slot t = n2w (LENGTH vs) /\
    abi_decode_sim ctx fn initial t
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decoder_loop_entry_code >> strip_tac >>
  qabbrev_tac `h = jump_to (fresh_label_output "dec_dyn_hdr" start.cs_next_label) initial` >>
  `abi_decode_sim ctx fn initial h` by
    (simp_tac bool_ss [Abbr`h`] >> irule abi_decoder_loop_entry_sim >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    start.cs_next_var limit_st fp initial
    (fresh_label_output "dec_dyn_hdr" start.cs_next_label) 0 h` by
    (simp_tac bool_ss [abi_decoder_primitive_loop_inv_def, Abbr`h`,
       abi_decoder_array_memory_jump, abi_decode_mload_jump] >>
     simp[jump_to_def, abi_decoder_loop_rel_jump]) >>
  drule_all abi_decoder_primitive_dyn_loop_from_header >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> metis_tac[abi_decode_sim_trans]
QED
