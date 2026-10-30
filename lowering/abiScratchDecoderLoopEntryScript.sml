(* Enter the actual finite source-valid loop from the initializer's runtime PC. *)
Theory abiScratchDecoderLoopEntry
Ancestors
  abiScratchDecoderContract abiScratchEncoderContract abiScratchArrayLoopEntry
  abiScratchDecoderDynLoop abiScratchDecoderLoopContext abiScratchDecoderLoopInvariant
  abiDecoderValidArrayMemory abiDecoderRecursiveLoopEntry abiDecoderRecursiveLoopLayout
  abiDecoderPrimitiveLoopEntry
  abiDecoderEffect abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderContract
  abiDecoderValidContract abiDecoderLoop abiDecoderReentry abiDecoderExecution abiDecoderTypedContract
  fragExec compileEnv valueEncoding vyperABI vyperValue venomState venomExecSemantics
  venomInst words list arithmetic

Theorem abi_scratch_decoder_loop_from_state:
  compile_abi_decode_dyn_loop dst src opc hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    ip cnt start = ((),final) /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= site /\ site < start.cs_next_id /\ final.cs_next_id <= hi /\ hi <= last /\
  next <= start.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial /\ abi_scratch_decoder ce env sf ty tv /\
  abi_decoder_valid_array_memory opc bs tv vs sb d 0 initial /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ mload slot initial = 0w /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_scratch_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w (LENGTH vs) /\
    t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by
    fs[abi_scratch_decoder_loop_data_def, abi_scratch_decoder_ranges_def,
      Excl "enc_def"] >>
  drule_all abi_decoder_recursive_entry_code >> strip_tac >>
  qabbrev_tac `h = jump_to (fresh_label_output "dec_dyn_hdr" start.cs_next_label) initial` >>
  `abi_decode_sim ctx func initial h` by
    (simp_tac bool_ss [Abbr`h`] >> irule abi_decoder_loop_entry_sim >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial
    (fresh_label_output "dec_dyn_hdr" start.cs_next_label) 0 h` by
    (simp_tac bool_ss [abi_scratch_decoder_loop_inv_def, Abbr`h`,
       abi_decoder_valid_array_memory_jump, abi_decode_mload_jump] >>
     simp[jump_to_def, abi_scratch_effect_jump]) >>
  drule_all abi_scratch_decoder_dyn_loop >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> metis_tac[abi_decode_sim_trans]
QED
