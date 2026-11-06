Theory calldataScratchLoopEntryPtr
Ancestors
  abiDecoderRecursiveLoopEntry abiDecoderPrimitiveLoopEntry typedCopyArrayPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomState emitHelperProps
  list venomInst

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
