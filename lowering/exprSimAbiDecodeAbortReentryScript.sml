(* Abort transport for the decoder's straight arithmetic/read guards. *)
Theory exprSimAbiDecodeAbortReentry
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend execEquivParamProps stateEquiv
  venomExecSemantics venomState venomInst exprLoweringProps list

Theorem abi_decode_assert_vars_extend_abort:
  abi_decoder_vars_extend extras s t /\ inst.inst_opcode = ASSERT /\
  step_inst_base inst s = Abort Revert_abort u ==>
  ?v. step_inst_base inst t = Abort Revert_abort v
Proof
  strip_tac >>
  `abi_decoder_inputs_defined inst s` by
    (gvs[abi_decoder_inputs_defined_def, step_inst_base_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[eval_operand_def]) >>
  drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
  mp_tac (Q.SPECL [`abi_decoder_vars_extend extras`,
    `\s t. vsr_term_frame s = vsr_term_frame t`, `0`, `ARB`, `inst`, `s`, `t`]
    step_inst_preserves_R) >>
  (impl_tac >- simp[abi_decoder_vars_extend_valid]) >>
  asm_simp_tac (srw_ss()) [step_inst_non_invoke] >>
  Cases_on `step_inst_base inst t` >> simp[lift_result_def] >> metis_tac[]
QED

Theorem abi_decode_guard_abort_opcode[local]:
  MEM inst.inst_opcode [ADD; MUL; LT; GT; AND; ISZERO; MLOAD; ASSERT] /\
  step_inst_base inst s = Abort a u ==> inst.inst_opcode = ASSERT /\ a = Revert_abort
Proof
  strip_tac >> fs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_rewrite_tac [Once step_inst_base_def, opcode_case_def] >>
  simp_tac (srw_ss()) [exec_pure1_def, exec_pure2_def, exec_read1_def,
      AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem abi_decode_guard_sequence_vars_extend_abort:
  !insts extras s t u.
  EVERY (\i. MEM i.inst_opcode [ADD; MUL; LT; GT; AND; ISZERO; MLOAD; ASSERT]) insts /\
  abi_decoder_vars_extend extras s t /\
  run_inst_seq insts s = Abort Revert_abort u ==>
  ?v. run_inst_seq insts t = Abort Revert_abort v
Proof
  Induct >- simp[run_inst_seq_def] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[]
  >>~- ([`step_inst_base inst s = OK v`],
      `abi_decoder_reentry_opcode inst.inst_opcode` by
        fs[abi_decoder_reentry_opcode_def] >>
      drule_all abi_decoder_step_vars_extend >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `v''` >> simp[run_inst_seq_def]) >>
  `MEM inst.inst_opcode [ADD; MUL; LT; GT; AND; ISZERO; MLOAD; ASSERT]` by simp[] >>
  drule_all abi_decode_guard_abort_opcode >> strip_tac >>
  drule_all abi_decode_assert_vars_extend_abort >> strip_tac >>
  qexists_tac `v` >> simp[run_inst_seq_def]
QED
