(* Enter the actual recursive loop from the initializer's runtime program point. *)
Theory abiDecoderRecursiveLoopEntry
Ancestors
  abiDecoderRecursiveDynLoop abiDecoderRecursiveLoopLayout abiDecoderLoopCode
  abiDecoderLoopEmit abiDecoderArraySetupCode abiDecoderRecursiveLoopContext
  abiDecoderRecursiveLoopInvariant abiDecoderPrimitiveLoopEntry abiDecoderArrayInvariant
  abiDecoderEffect abiDecoderDynamicLoopSetup abiDecoderLoopRegisters
  abiDecoderAllocation abiDecoderContract abiDecoderCorrect abiDecoderLoop abiDecoderReentry
  abiDecoderExecution abiDecoderTypedContract
  fragExec compileEnv emitHelperProps emitHelper valueEncoding
  venomState venomExecSemantics venomInst words list arithmetic

Theorem abi_decoder_completed_loop_entry:
  fn_has_code start final func /\ st.cs_blocks = header::entry::start.cs_blocks /\
  end_st.cs_blocks = children ++ st.cs_blocks /\ final.cs_blocks = back::end_st.cs_blocks ==>
  lookup_block entry.bb_label func.fn_blocks = SOME entry
Proof
  strip_tac >>
  `final.cs_blocks = (back::children ++ [header;entry]) ++ start.cs_blocks` by simp[APPEND_ASSOC] >>
  mp_tac (Q.INST [`st` |-> `start:compile_state`, `end_st` |-> `final:compile_state`,
    `added` |-> `back::children ++ [header;entry]:basic_block list`,
    `bb` |-> `entry:basic_block`] abi_decoder_code_completed) >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_decoder_loop_phase_entry:
  abi_decode_loop_prefix ip src opc start = (labels,st) /\
  abi_decode_array_element_setup ip src dst opc hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code start final func ==>
  lookup_block start.cs_current_bb func.fn_blocks = SOME
    <|bb_label := start.cs_current_bb; bb_instructions := start.cs_current_insts ++
      [mk_inst start.cs_next_id JMP [Label (FST labels)] []]|>
Proof
  strip_tac >> drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `?children. end_st.cs_blocks = children ++ st.cs_blocks` by fs[cs_extends_def] >>
  drule_all abi_decoder_completed_loop_entry >> simp[]
QED

Theorem abi_decoder_recursive_entry_code:
  compile_abi_decode_dyn_loop dst src opc hi di asz msz ip cnt start = ((),final) /\
  fn_has_code start final func /\ abi_decode_source_opcode opc ==>
  ?bb hdr_bb. lookup_block start.cs_current_bb func.fn_blocks = SOME bb /\
    bb.bb_instructions = start.cs_current_insts ++ [mk_inst start.cs_next_id JMP
      [Label (fresh_label_output "dec_dyn_hdr" start.cs_next_label)] []] /\
    lookup_block (fresh_label_output "dec_dyn_hdr" start.cs_next_label) func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0
Proof
  strip_tac >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule_all abi_decoder_loop_phase_entry >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >>
  gvs[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decoder_effect_jump:
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s (jump_to hdr s)
Proof
  strip_tac >>
  `abi_decoder_address_frame next s (jump_to hdr s)` by
    simp[abi_decoder_address_frame_def, abi_decoder_operand_jump, jump_to_def] >>
  `fresh_vars_wrt limit_st (jump_to hdr s)` by simp[jump_to_def, fresh_vars_wrt_def] >>
  irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >> qexists_tac `next` >> simp[]
QED

Theorem abi_decoder_recursive_loop_from_state:
  compile_abi_decode_dyn_loop dst src opc hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    ip cnt start = ((),final) /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= site /\ site < start.cs_next_id /\ final.cs_next_id <= hi /\ hi <= last /\
  next <= start.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi_op ip src dst
    sb d slot b cap next initial /\ abi_decoder_correct ce env sf ty tv /\
  abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 initial /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ mload slot initial = 0w /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_decoder_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w (LENGTH vs) /\
    t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_loop_data_def, abi_decoder_ranges_def,
      Excl "enc_def"] >>
  drule_all abi_decoder_recursive_entry_code >> strip_tac >>
  qabbrev_tac `h = jump_to (fresh_label_output "dec_dyn_hdr" start.cs_next_label) initial` >>
  `abi_decode_sim ctx func initial h` by
    (simp_tac bool_ss [Abbr`h`] >> irule abi_decoder_loop_entry_sim >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `abi_decoder_recursive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial
    (fresh_label_output "dec_dyn_hdr" start.cs_next_label) 0 h` by
    (simp_tac bool_ss [abi_decoder_recursive_loop_inv_def, Abbr`h`,
       abi_decoder_array_memory_jump, abi_decode_mload_jump] >>
     simp[jump_to_def, abi_decoder_effect_jump]) >>
  drule_all abi_decoder_recursive_dyn_loop >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> metis_tac[abi_decode_sim_trans]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_RECURSIVE_LOOP_ENTRY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI recursive loop entry not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderRecursiveLoopEntry");
