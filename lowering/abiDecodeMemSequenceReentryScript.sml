(* Memory checks and finite replay tolerate stale decoder temporaries. *)
Theory abiDecodeMemSequenceReentry
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend execEquivParamDefs
  codegenRel contextCodegenRel memSafeRun unitTransformDefs
  opcodeClass venomExecSemantics venomState venomInst
  fragExecMem exprLoweringProps finite_map list

Theorem abi_decode_reentry_operand_agreement:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  Cases >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem abi_decode_reentry_memory_checks:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s /\
  abi_decoder_reentry_opcode inst.inst_opcode ==>
  (inst_mem_below_frontier inst s <=> inst_mem_below_frontier inst t) /\
  (inst_dload_in_section inst s <=> inst_dload_in_section inst t)
Proof
  strip_tac >> drule abi_decode_reentry_operand_agreement >> disch_then drule >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def, inst_dload_in_section_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> fs[fixed_source_write_range_def, sized_source_write_range_def] >>
  rename1 `h::h'::rest` >> Cases_on `rest` >> fs[fixed_source_write_range_def, sized_source_write_range_def] >>
  rename1 `h::h'::h''::rest` >> Cases_on `rest` >> fs[fixed_source_write_range_def, sized_source_write_range_def] >>
  fs[fixed_source_write_range_def, sized_source_write_range_def]
QED

Theorem abi_decode_reentry_revert:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s /\
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort Revert_abort u ==>
  ?v. step_inst_base inst t = Abort Revert_abort v /\
      abi_decoder_vars_extend extras u v
Proof
  strip_tac >>
  `inst.inst_opcode = ASSERT` by
    (drule opcodeClassTheory.step_inst_base_abort_opcodes >>
     fs[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  drule abi_decode_reentry_operand_agreement >> disch_then drule >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[step_inst_base_def] >>
  simp[abi_decoder_vars_extend_def, vsr_frame_def, abi_decoder_var_map_def,
    revert_state_def, set_returndata_def, Excl "vsr_complete_mask_equality"] >>
  fs[abi_decoder_vars_extend_def, vsr_frame_def, abi_decoder_var_map_def,
     Excl "vsr_complete_mask_equality"] >>
  qpat_x_assum `s with vs_vars := FEMPTY = _`
    (mp_tac o Q.AP_TERM `\u:venom_state. u with <|vs_returndata := []; vs_halted := T|>`) >> simp[]
QED


Theorem abi_decode_revert_inputs[local]:
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort Revert_abort u ==>
  abi_decoder_inputs_defined inst s
Proof
  strip_tac >>
  `inst.inst_opcode = ASSERT` by
    (drule opcodeClassTheory.step_inst_base_abort_opcodes >>
     fs[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_def] >> strip_tac >>
  gvs[AllCaseEqs(), abi_decoder_inputs_defined_def, eval_operand_def] >>
  rpt strip_tac >> gvs[eval_operand_def]
QED

Theorem abi_decode_sequence_revert_extend:
  !code extras s t u.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  abi_decoder_vars_extend extras s t /\
  run_inst_seq code s = Abort Revert_abort u ==>
  ?v. run_inst_seq code t = Abort Revert_abort v /\
    abi_decoder_vars_extend extras u v
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[]
  >- (drule_all abi_decoder_step_vars_extend >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      goal_assum (drule_at Any) >> simp[run_inst_seq_def]) >>
  drule_all abi_decode_revert_inputs >> strip_tac >>
  drule_all abi_decode_reentry_revert >> strip_tac >>
  goal_assum (drule_at Any) >> simp[run_inst_seq_def]
QED

Theorem abi_decode_sequence_mem_extend:
  !code extras s t.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  abi_decoder_vars_extend extras s t /\
  ((?u. run_inst_seq code s = OK u) \/
   (?u. run_inst_seq code s = Abort Revert_abort u)) /\
  run_inst_seq_mem_ok code s ==>
  run_inst_seq_mem_ok code t
Proof
  Induct >- simp[run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, run_inst_seq_def,
    run_inst_seq_mem_ok_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[]
  >>~- ([`step_inst_base h s = OK v`],
    drule_all abi_decoder_step_inputs_defined >> strip_tac >>
    drule_all abi_decode_reentry_memory_checks >> strip_tac >>
    drule_all abi_decoder_step_vars_extend >> strip_tac >>
    simp[] >> rpt conj_tac >- metis_tac[] >- metis_tac[] >>
    first_x_assum irule >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all abi_decode_revert_inputs >> strip_tac >>
  drule_all abi_decode_reentry_memory_checks >> strip_tac >>
  drule_all abi_decode_reentry_revert >> strip_tac >> simp[] >> metis_tac[]
QED

