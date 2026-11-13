Theory ctorDeployMemoryRunMemEntrySequenceWorld
Ancestors
  ctorAbiActualWorld abiDecoderVarSequence exprLoweringProps
  venomExecSemantics venomState list

Theorem ctor_decoder_step_context_world:
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = OK t ==>
  t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_outcomes = s.vs_outcomes
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def] >>
  fs[step_inst_base_opcode_eqs] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
      exec_alloca_def, AllCaseEqs()] >>
  simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def,
       jump_to_def]
QED

Theorem ctor_decoder_sequence_context_world:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_outcomes = s.vs_outcomes
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all ctor_decoder_step_context_world >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
