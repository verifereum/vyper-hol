(* Frontier checks survive replay with unused temporary bindings. *)
Theory abiDecodeMemReentry
Ancestors
  abiDecodePtrReentryObservations abiDecoderVarSequence abiDecoderVarExtend
  abiEncoderVarTransport fragExecMem fragExec exprLoweringProps memSafeRun instMemFrontier
  contextCodegenRel unitTransformDefs venomExecSemantics venomState venomInst list

Theorem abi_decode_mem_reentry_inst:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s /\
  abi_decoder_reentry_opcode inst.inst_opcode ==>
  (inst_mem_below_frontier inst s <=> inst_mem_below_frontier inst t) /\
  (inst_dload_in_section inst s <=> inst_dload_in_section inst t)
Proof
  strip_tac >>
  drule_all abi_decode_ptr_reentry_read_ranges >> strip_tac >>
  drule_all abi_decode_ptr_reentry_write_ranges >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  simp[inst_mem_below_frontier_def] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    metis_tac[abi_decode_ptr_reentry_eval] >>
  simp[inst_dload_in_section_def] >> eq_tac >> rpt strip_tac >>
  `eval_operand op s = eval_operand op t` by
    (first_x_assum irule >> fs[]) >> metis_tac[]
QED

Theorem abi_decode_sequence_mem_reentry:
  !insts extras s t u.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  abi_decoder_vars_extend extras s t /\ run_inst_seq insts s = OK u /\
  run_inst_seq_mem_ok insts s ==>
  run_inst_seq_mem_ok insts t
Proof
  Induct >- simp[run_inst_seq_mem_ok_def] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, run_inst_seq_def, run_inst_seq_mem_ok_def] >>
  strip_tac >> Cases_on `step_inst_base inst s` >> gvs[] >>
  rename1 `step_inst_base inst s = OK mid` >>
  `abi_decoder_inputs_defined inst s` by
    metis_tac[abi_decoder_step_inputs_defined] >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  drule_all abi_decode_mem_reentry_inst >> strip_tac >>
  `inst_mem_below_frontier inst t /\ inst_dload_in_section inst t` by
    metis_tac[] >> simp[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
