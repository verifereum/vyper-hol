(* Execute the real initial JMP and establish the precise finite-loop invariant.
   TOP-LEVEL: abi_scratch_array_loop_enter starts at index zero without changing
   the source, output, cursor observations or physical scratch footprint. *)
Theory abiScratchArrayLoopEntry
Ancestors
  abiScratchArrayLoopInvariant abiScratchAddressEffect abiScratchEncoderContract
  abiEncoderArrayLoopEntry abiEncoderArrayLoopCode abiEncoderMembersDefs
  abiDecoderDynamicLoopSetup abiDecoderLoopRegisters abiDecoderFootprint abiDecoderLoop
  abiDecoderReentry compileEnv valueEncoding contractABI venomState venomExecSemantics words list arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_LOOP_ENTRY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch actual loop entry not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayLoopEntry");
