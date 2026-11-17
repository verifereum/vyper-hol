(* Runtime reentry for malformed ABI inputs, including revert outcomes. *)
Theory abiDecoderAbortReentry
Ancestors
  abiDecoderVarSequence abiDecoderReentryPointer abiDecoderVarExtend
  execEquivParamProps execEquivParamDefs stateEquiv
  venomExecSemantics venomState venomInst exprLoweringProps compileEnv loweringStateRelDefs
  abiDecoderReentry finite_map arithmetic list option

Theorem abi_decoder_revert_inputs:
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort Revert_abort u ==>
  abi_decoder_inputs_defined inst s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs,
    exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), abi_decoder_inputs_defined_def,
    eval_operand_def] >> rpt strip_tac >> gvs[eval_operand_def]
QED

Theorem abi_decoder_revert_vars_extend:
  abi_decoder_vars_extend extras s t /\
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort Revert_abort u ==>
  ?v. step_inst_base inst t = Abort Revert_abort v
Proof
  strip_tac >> drule_all abi_decoder_revert_inputs >> strip_tac >>
  drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
  drule_all abi_decoder_reentry_non_invoke >> strip_tac >>
  mp_tac (Q.SPECL [`abi_decoder_vars_extend extras`,
    `\s t. vsr_term_frame s = vsr_term_frame t`, `0`, `ARB`, `inst`, `s`, `t`]
    step_inst_preserves_R) >>
  impl_tac >- simp[abi_decoder_vars_extend_valid] >>
  asm_simp_tac (srw_ss()) [step_inst_non_invoke] >>
  Cases_on `step_inst_base inst t` >> simp[lift_result_def] >> metis_tac[]
QED

Theorem abi_decoder_sequence_revert_vars_extend:
  !insts extras s t u.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  abi_decoder_vars_extend extras s t /\
  run_inst_seq insts s = Abort Revert_abort u ==>
  ?v. run_inst_seq insts t = Abort Revert_abort v
Proof
  Induct >- simp[run_inst_seq_def] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[]
  >- (drule_all abi_decoder_step_vars_extend >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      simp[run_inst_seq_def] >> metis_tac[]) >>
  drule_all abi_decoder_revert_vars_extend >> strip_tac >>
  qexists_tac `v` >> simp[run_inst_seq_def]
QED

Theorem abi_decoder_sequence_revert_reentry:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  run_inst_seq insts (abi_decoder_prune_vars next initial) =
    Abort Revert_abort clean ==>
  ?actual. run_inst_seq insts initial = Abort Revert_abort actual
Proof
  strip_tac >>
  `abi_decoder_vars_extend initial.vs_vars
     (abi_decoder_prune_vars next initial) initial` by
    irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_revert_vars_extend >> simp[]
QED

Theorem abi_decoder_sequence_runtime_reentry:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  run_inst_seq insts (abi_decoder_prune_vars next initial) = OK clean /\
  fresh_vars_wrt last clean /\ fresh_vars_wrt last initial ==>
  ?actual. run_inst_seq insts initial = OK actual /\
    abi_decoder_vars_extend initial.vs_vars clean actual /\
    fresh_vars_wrt last actual /\
    (!op w. eval_operand op clean = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_memory = clean.vs_memory /\
    actual.vs_call_ctx = clean.vs_call_ctx /\
    actual.vs_data_section = clean.vs_data_section /\
    actual.vs_allocas = clean.vs_allocas /\
    actual.vs_alloca_next = clean.vs_alloca_next
Proof
  strip_tac >>
  `abi_decoder_vars_extend initial.vs_vars
     (abi_decoder_prune_vars next initial) initial` by
    irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  `!n. last.cs_next_var <= n ==>
     STRING #"%" (toString n) NOTIN FDOM initial.vs_vars` by
    fs[fresh_vars_wrt_def, GREATER_EQ] >>
  drule_all abi_decoder_vars_extend_fresh >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  qexists_tac `v` >> simp[] >> metis_tac[abi_decoder_vars_extend_eval]
QED
