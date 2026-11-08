Theory calldataScratchLoopEntryPtr
Ancestors
  abiDecoderRecursiveLoopEntry abiDecoderPrimitiveLoopEntry typedCopyArrayPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomState emitHelperProps
  list venomInst abiDecoderRecursiveLoopLayout abiDecoderLoopEmit
  abiScratchDecoderLoopContext abiScratchDecoderLoopInvariant bodyPtrDefs
  abiScratchEncoderContract abiScratchFootprint abiDecoderAllocation abiDecoderFrame
  compileEnv abiScratchDecoderContract abiScratchEffect abiDecoderReentry
  abiScratchDecoderLoopControl abiDecoderValidArrayMemory

Theorem calldata_scratch_loop_entry_ptr:
  compile_abi_decode_dyn_loop dst src opc hi di asz msz ip cnt start = ((),final) /\
  fn_has_code start final func /\ abi_decode_source_opcode opc /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  abi_decode_sim ctx func s
    (jump_to (fresh_label_output "dec_dyn_hdr" start.cs_next_label) s) /\
  ((!fuel. ptr_safe_run D lower fuel ctx func PG G tn
    (jump_to (fresh_label_output "dec_dyn_hdr" start.cs_next_label) s)) ==>
   !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_recursive_entry_code >> strip_tac >>
  conj_tac
  >- (irule abi_decoder_loop_entry_sim >> goal_assum (drule_at Any) >>
      asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst start.cs_next_id JMP
      [Label (fresh_label_output "dec_dyn_hdr" start.cs_next_label)] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `!fuel. ptr_safe_step D lower fuel ctx func PG G tn
    (mk_inst start.cs_next_id JMP
      [Label (fresh_label_output "dec_dyn_hdr" start.cs_next_label)] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, step_inst_non_invoke, step_inst_base_def, jump_to_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          op_taint_def]) >>
  fs[] >> strip_tac >> Cases_on `fuel`
  >- (simp[Once ptr_safe_run_def, Once ptr_safe_block_def,
           get_instruction_def, EL_APPEND_EQN] >>
      simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
           is_terminator_def, Once ptr_safe_blocks_def]) >>
  `is_terminator (mk_inst start.cs_next_id JMP
      [Label (fresh_label_output "dec_dyn_hdr" start.cs_next_label)] []).inst_opcode /\
   (mk_inst start.cs_next_id JMP
      [Label (fresh_label_output "dec_dyn_hdr" start.cs_next_label)] []).inst_opcode <> INVOKE /\
   step_inst_base (mk_inst start.cs_next_id JMP
      [Label (fresh_label_output "dec_dyn_hdr" start.cs_next_label)] []) s =
     OK (jump_to (fresh_label_output "dec_dyn_hdr" start.cs_next_label) s)` by
    simp[mk_inst_def, is_terminator_def, step_inst_base_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all ptr_safe_run_jump_no_phi >>
  disch_then (qspecl_then [`n`,`D`,`lower`,`ctx`,`PG`,`G`,`tn`] mp_tac) >>
  simp[]
QED

Theorem abi_decoder_compiled_dyn_loop_layout:
  compile_abi_decode_dyn_loop dst src opc hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    ip cnt start = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= site /\ site < start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ next <= start.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?labels st ops middle end_st.
    abi_decode_loop_prefix ip src opc start = (labels,st) /\
    abi_decode_array_element_setup ip src dst opc hi_op (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi_op
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
    abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
      (FST labels) (SND (SND labels)) (start.cs_next_id+1) start.cs_next_var
      first last lo hi next limit_st site
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  qexistsl_tac [`labels`, `st0`, `ops`, `middle`, `st1`] >>
  asm_rewrite_tac[] >> irule abi_decoder_recursive_loop_layout >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  qexists_tac `final` >> asm_rewrite_tac[]
QED

Theorem decoder_live_operand_jump:
  abi_decoder_operand_live next op ==>
  eval_operand op (jump_to lbl s) = eval_operand op s
Proof
  Cases_on `op` >> simp[abi_decoder_operand_live_def, eval_operand_def,
    lookup_var_def, jump_to_def]
QED

Theorem decoder_jump_fields:
  (jump_to lbl s).vs_vars = s.vs_vars /\
  (jump_to lbl s).vs_alloca_next = s.vs_alloca_next /\
  (jump_to lbl s).vs_allocas = s.vs_allocas /\
  (jump_to lbl s).vs_memory = s.vs_memory /\
  (jump_to lbl s).vs_call_ctx = s.vs_call_ctx /\
  (jump_to lbl s).vs_data_section = s.vs_data_section /\
  (jump_to lbl s).vs_halted = s.vs_halted
Proof
  simp[jump_to_def]
QED

Theorem decoder_fresh_vars_jump:
  fresh_vars_wrt limit_st (jump_to lbl s) = fresh_vars_wrt limit_st s
Proof
  simp_tac bool_ss [fresh_vars_wrt_def, decoder_jump_fields]
QED

Theorem decoder_budget_jump:
  abi_decoder_budget first last b cap (jump_to lbl s) =
  abi_decoder_budget first last b cap s
Proof
  simp_tac bool_ss [abi_decoder_budget_def, abi_decoder_missing_def, decoder_jump_fields]
QED

Theorem decoder_scratch_evolution_jump:
  abi_scratch_evolution ids b cap initial (jump_to lbl s) =
  abi_scratch_evolution ids b cap initial s
Proof
  simp_tac bool_ss [abi_scratch_evolution_def, decoder_jump_fields]
QED

Theorem decoder_footprint_frame_jump:
  abi_decode_footprint_frame fp initial (jump_to lbl s) =
  abi_decode_footprint_frame fp initial s
Proof
  simp_tac bool_ss [abi_decode_footprint_frame_def, decoder_jump_fields]
QED

Theorem abi_scratch_effect_jump:
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial s ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial (jump_to lbl s)
Proof
  simp_tac bool_ss [abi_scratch_effect_def, decoder_fresh_vars_jump, decoder_budget_jump,
    decoder_scratch_evolution_jump, decoder_footprint_frame_jump, decoder_jump_fields] >>
  strip_tac >> asm_rewrite_tac[] >> rpt strip_tac >>
  drule decoder_live_operand_jump >> simp[]
QED

Theorem abi_scratch_decoder_loop_inv_entry_jump:
  abi_decoder_valid_array_memory opc bs tv vs sb d 0 s /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\ mload slot s = 0w /\
  ~s.vs_halted ==>
  abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap s hdr 0 (jump_to hdr s)
Proof
  strip_tac >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap s s` by
    simp[abi_scratch_effect_refl] >>
  drule abi_scratch_effect_jump >> disch_then (qspec_then `hdr` assume_tac) >>
  simp[abi_scratch_decoder_loop_inv_def] >>
  fs[jump_to_def, mload_def]
QED

Theorem decoder_child_scratch_jump:
  abi_decoder_child_scratch ids b cap (jump_to lbl s) =
  abi_decoder_child_scratch ids b cap s
Proof
  simp_tac bool_ss [abiDecoderFootprintTheory.abi_decoder_child_scratch_def,
    decoder_jump_fields]
QED

Theorem abi_scratch_decoder_ranges_jump:
  abi_scratch_decoder_ranges opc hi_op src dst sb len d outsz first last b cap s /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op ==>
  abi_scratch_decoder_ranges opc hi_op src dst sb len d outsz first last b cap
    (jump_to lbl s)
Proof
  strip_tac >>
  `eval_operand src (jump_to lbl s) = eval_operand src s /\
   eval_operand dst (jump_to lbl s) = eval_operand dst s /\
   eval_operand hi_op (jump_to lbl s) = eval_operand hi_op s` by
    metis_tac[decoder_live_operand_jump] >>
  fs[abi_scratch_decoder_ranges_def, decoder_child_scratch_jump, Excl "enc_def"] >>
  disj2_tac >> qexists_tac `h` >> simp[]
QED

Theorem abi_scratch_decoder_loop_data_jump:
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next s ==>
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next (jump_to lbl s)
Proof
  simp_tac bool_ss [abi_scratch_decoder_loop_data_def] >> strip_tac >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule abi_scratch_decoder_ranges_jump >> goal_assum (drule_at Any) >>
      qexists_tac `next` >> asm_rewrite_tac[]) >>
  drule decoder_live_operand_jump >> simp[]
QED

Theorem calldata_scratch_compiled_loop_entry_ptr:
  compile_abi_decode_dyn_loop dst src opc hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    ip cnt start = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= site /\ site < start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ next <= start.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_valid_array_memory opc bs tv vs sb d 0 s /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\ mload slot s = 0w /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?labels st ops middle end_st.
    abi_decode_loop_prefix ip src opc start = (labels,st) /\
    abi_decode_array_element_setup ip src dst opc hi_op (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi_op
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
    abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
      (FST labels) (SND (SND labels)) (start.cs_next_id+1) start.cs_next_var
      first last lo hi next limit_st site /\
    abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
      first last lo hi next limit_st b cap s
      (FST labels) 0 (jump_to (FST labels) s) /\
    abi_decode_sim ctx func s (jump_to (FST labels) s) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG G tn
      (jump_to (FST labels) s)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_compiled_dyn_loop_layout >> strip_tac >>
  drule_all calldata_scratch_loop_entry_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `FST labels = fresh_label_output "dec_dyn_hdr" start.cs_next_label` by
    (qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_loop_prefix_shape, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >>
  qexistsl_tac [`labels`,`st`,`ops`,`middle`,`end_st`] >>
  asm_rewrite_tac[] >> irule abi_scratch_decoder_loop_inv_entry_jump >>
  asm_rewrite_tac[]
QED
