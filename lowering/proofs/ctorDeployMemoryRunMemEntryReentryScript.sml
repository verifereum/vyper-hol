Theory ctorDeployMemoryRunMemEntryReentry
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend fragExecMem
  instMemFrontier memSafeRun unitTransformDefs contextCodegenRel codegenRel
  exprLoweringProps venomExecSemantics venomState venomInst list

Theorem ctor_reentry_operand_agreement:
  abi_decoder_vars_extend extras s t /\
  abi_decoder_inputs_defined inst s /\ MEM op inst.inst_operands ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >> drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem ctor_reentry_step_mem:
  abi_decoder_vars_extend extras s t /\
  abi_decoder_reentry_opcode i.inst_opcode /\ step_inst_base i s = OK u /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s ==>
  inst_mem_below_frontier i t /\ inst_dload_in_section i t
Proof
  strip_tac >> drule_all abi_decoder_step_inputs_defined >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  `!op. MEM op i.inst_operands ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> irule ctor_reentry_operand_agreement >> metis_tac[]) >>
  Cases_on `i.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def] >>
  fs[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, fixed_source_write_range_def,
     sized_source_write_range_def, inst_dload_in_section_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  rename1 `i.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[] >>
  rename1 `i.inst_operands = a::b::rest` >>
  Cases_on `rest` >> gvs[] >>
  rename1 `i.inst_operands = a::b::c::rest` >>
  Cases_on `rest` >> gvs[]
QED

Theorem ctor_reentry_sequence_mem:
  !code extras s t u.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  abi_decoder_vars_extend extras s t /\ run_inst_seq code s = OK u /\
  run_inst_seq_mem_ok code s ==>
  run_inst_seq_mem_ok code t
Proof
  Induct >> simp[run_inst_seq_def, run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all ctor_reentry_step_mem >> strip_tac >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  simp[] >> first_x_assum irule >> metis_tac[]
QED
