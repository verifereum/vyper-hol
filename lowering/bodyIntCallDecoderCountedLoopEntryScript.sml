(* Physical finite decoder execution through layout and the entry jump. *)
Theory bodyIntCallDecoderCountedLoopEntry
Ancestors
  bodyIntCallDecoderCountedLoopFinite bodyIntCallDecoderCountedContract
  bodyIntCallDecoderCountedControl abiScratchDecoderDynLoop
  abiScratchDecoderLoopEntry abiScratchDecoderContract abiScratchEncoderContract
  abiScratchArrayLoopRun abiDecoderRecursiveLoopLayout abiDecoderRecursiveLoopContext
  abiScratchDecoderLoopContext abiScratchDecoderLoopInvariant abiDecoderLoopEmit
  abiDecoderArraySetupCode abiDecoderValidContract abiDecoderEffect abiDecoderExecution
  abiDecoderLoop abiDecoderTypedContract abiDecoderContract abiDecoderValidArrayMemory
  abiDecoderRecursiveLoopEntry abiDecoderPrimitiveLoopEntry abiDecoderDynamicLoopSetup
  abiDecoderAllocation abiDecoderReentry fragExec fragGasPath compileEnv valueEncoding
  vyperABI vyperValue venomState venomExecSemantics venomInst words list arithmetic

Theorem intcall_scratch_decoder_dyn_loop:
  compile_abi_decode_dyn_loop dst src opc base_op hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    ip cnt start = ((),final) /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= site /\ site < start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ next <= start.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc base_op hi_op ip src dst
    B sb d slot first last b cap next initial /\ intcall_scratch_decoder_counted ce env sf ty tv /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial
    (fresh_label_output "dec_dyn_hdr" start.cs_next_label) i s ==>
  ?t n. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_scratch_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w (LENGTH vs) /\
    t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ ~t.vs_halted /\ gas_path ctx func s n (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by
    fs[abi_scratch_decoder_loop_data_def, abi_scratch_decoder_ranges_def,
      Excl "enc_def"] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule_all abi_decoder_recursive_loop_layout >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >> gvs[Excl "enc_def"] >>
  drule intcall_scratch_decoder_loop_typed >>
  simp_tac bool_ss [] >> disch_then drule_all >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> qexistsl_tac [`t`, `n`] >> simp[]
QED

Theorem intcall_decoder_entry_jump_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  gas_path ctx func s 0 (OK (jump_to hdr s))
Proof
  strip_tac >> irule intcall_jump_step_path >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`bb`, `mk_inst id JMP [Label hdr] []`] >>
  simp[get_instruction_def, EL_APPEND_EQN, mk_inst_def, is_terminator_def,
    Once step_inst_base_def]
QED

Theorem intcall_scratch_decoder_loop_from_state:
  compile_abi_decode_dyn_loop dst src opc base_op hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    ip cnt start = ((),final) /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= site /\ site < start.cs_next_id /\ final.cs_next_id <= hi /\ hi <= last /\
  next <= start.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc base_op hi_op ip src dst
    B sb d slot first last b cap next initial /\ intcall_scratch_decoder_counted ce env sf ty tv /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_decoder_valid_array_memory opc bs tv vs (B + sb) d 0 initial /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ mload slot initial = 0w /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t n. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_scratch_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w (LENGTH vs) /\
    t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ ~t.vs_halted /\ gas_path ctx func initial n (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by
    fs[abi_scratch_decoder_loop_data_def, abi_scratch_decoder_ranges_def,
      Excl "enc_def"] >>
  drule_all abi_decoder_recursive_entry_code >> strip_tac >>
  qabbrev_tac `h = jump_to (fresh_label_output "dec_dyn_hdr" start.cs_next_label) initial` >>
  `gas_path ctx func initial 0 (OK h)` by
    (simp_tac bool_ss [Abbr`h`] >> irule intcall_decoder_entry_jump_path >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial
    (fresh_label_output "dec_dyn_hdr" start.cs_next_label) 0 h` by
    (simp_tac bool_ss [abi_scratch_decoder_loop_inv_def, Abbr`h`,
       abi_decoder_valid_array_memory_jump, abi_decode_mload_jump] >>
     simp[jump_to_def, abi_scratch_effect_jump]) >>
  drule_all intcall_scratch_decoder_dyn_loop >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> metis_tac[gas_path_then, ADD_CLAUSES]
QED
