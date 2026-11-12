Theory abiDecodePtrAbortReentry
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend execEquivParamProps execEquivParamDefs
  stateEquiv exprLoweringProps fragExec venomExecSemantics venomExecProofs venomState venomInst list

(* Only the executed prefix and the rejecting instruction need defined inputs.
   There is deliberately no condition on the unexecuted suffix. *)
Theorem abi_decode_rejecting_prefix_reentry:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) pre /\
  abi_decoder_reentry_opcode bad.inst_opcode /\
  run_inst_seq pre s = OK r /\
  step_inst_base bad r = Abort Revert_abort u /\
  abi_decoder_inputs_defined bad r /\
  abi_decoder_vars_extend extras s t ==>
  ?r' u'. run_inst_seq pre t = OK r' /\
    abi_decoder_vars_extend extras r r' /\
    step_inst_base bad r' = Abort Revert_abort u' /\
    vsr_term_frame u = vsr_term_frame u' /\
    run_inst_seq (pre ++ bad::post) t = Abort Revert_abort u'
Proof
  strip_tac >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  qpat_x_assum `abi_decoder_vars_extend extras s t` kall_tac >>
  rename1 `run_inst_seq pre t = OK reached` >>
  `!x. MEM (Var x) bad.inst_operands ==> lookup_var x r = lookup_var x reached` by
    metis_tac[abi_decoder_vars_extend_inputs] >>
  drule_all abi_decoder_reentry_non_invoke >> strip_tac >>
  mp_tac (Q.SPECL [`abi_decoder_vars_extend extras`,
    `\s t. vsr_term_frame s = vsr_term_frame t`, `0`, `ARB`, `bad`, `r`, `reached`]
    step_inst_preserves_R) >>
  (impl_tac >- simp[abi_decoder_vars_extend_valid]) >>
  asm_simp_tac (srw_ss()) [step_inst_non_invoke] >>
  Cases_on `step_inst_base bad reached` >> simp[lift_result_def] >>
  strip_tac >> gvs[] >>
  drule_at (Pat `run_inst_seq pre t = OK reached`) run_inst_seq_append >>
  disch_then (qspec_then `bad::post` mp_tac) >>
  simp[run_inst_seq_def]
QED
