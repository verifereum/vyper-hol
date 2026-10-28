(* Successful decoder sequences tolerate old values in generated temporaries. *)
Theory abiDecoderVarSequence
Ancestors
  abiDecoderVarExtend execEquivParamProps execEquivParamDefs stateEquiv
  exprLoweringProps venomExecSemantics venomState venomInst list option

Definition abi_decoder_reentry_opcode_def:
  abi_decoder_reentry_opcode opc <=>
    MEM opc [ADD;MUL;EQ;LT;GT;ISZERO;SHL;SHR;SIGNEXTEND;MLOAD;MSTORE;MCOPY;
      CALLDATALOAD;CALLDATACOPY;DLOAD;DLOADBYTES;ASSERT;ALLOCA;JMP;JNZ]
End

Definition abi_decoder_inputs_defined_def:
  abi_decoder_inputs_defined inst s <=>
    !x. MEM (Var x) inst.inst_operands ==> IS_SOME (lookup_var x s)
End

Theorem abi_decoder_reentry_non_invoke:
  abi_decoder_reentry_opcode opc ==> opc <> INVOKE
Proof
  rw[abi_decoder_reentry_opcode_def]
QED

Theorem abi_decoder_pure1_inputs:
  exec_pure1 f inst s = OK u ==> abi_decoder_inputs_defined inst s
Proof
  rw[exec_pure1_def, abi_decoder_inputs_defined_def] >>
  gvs[AllCaseEqs()] >> gvs[eval_operand_def]
QED

Theorem abi_decoder_pure2_inputs:
  exec_pure2 f inst s = OK u ==> abi_decoder_inputs_defined inst s
Proof
  rw[exec_pure2_def, abi_decoder_inputs_defined_def] >>
  gvs[AllCaseEqs()] >> gvs[eval_operand_def]
QED

Theorem abi_decoder_read1_inputs:
  exec_read1 f inst s = OK u ==> abi_decoder_inputs_defined inst s
Proof
  rw[exec_read1_def, abi_decoder_inputs_defined_def] >>
  gvs[AllCaseEqs()] >> gvs[eval_operand_def]
QED

Theorem abi_decoder_write2_inputs:
  exec_write2 f inst s = OK u ==> abi_decoder_inputs_defined inst s
Proof
  rw[exec_write2_def, abi_decoder_inputs_defined_def] >>
  gvs[AllCaseEqs()] >> gvs[eval_operand_def]
QED

Theorem abi_decoder_inline_inputs:
  MEM inst.inst_opcode [MCOPY; CALLDATACOPY; DLOADBYTES; ASSERT; ALLOCA; JMP; JNZ] /\
  step_inst_base inst s = OK u ==> abi_decoder_inputs_defined inst s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  rw[abi_decoder_inputs_defined_def] >>
  gvs[AllCaseEqs()] >> gvs[eval_operand_def]
QED

(* The premise is actual successful execution, not an assumed read set. The
   ALLOCA, JMP and JNZ cases also check their literal/label operand envelopes. *)
Theorem abi_decoder_step_inputs_defined:
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK u ==>
  abi_decoder_inputs_defined inst s
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode
    [MCOPY; CALLDATACOPY; DLOADBYTES; ASSERT; ALLOCA; JMP; JNZ]`
  >- (irule abi_decoder_inline_inputs >> simp[] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  metis_tac[abi_decoder_pure1_inputs, abi_decoder_pure2_inputs,
            abi_decoder_read1_inputs, abi_decoder_write2_inputs]
QED

Theorem abi_decoder_vars_extend_inputs:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  !x. MEM (Var x) inst.inst_operands ==> lookup_var x s = lookup_var x t
Proof
  rpt strip_tac >>
  `IS_SOME (lookup_var x s)` by fs[abi_decoder_inputs_defined_def] >>
  Cases_on `lookup_var x s` >> gvs[] >>
  rename1 `lookup_var x s = SOME w` >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  drule_all abi_decoder_vars_extend_eval >> simp[eval_operand_def]
QED

Theorem abi_decoder_step_vars_extend:
  abi_decoder_vars_extend extras s t /\
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK u ==>
  ?v. step_inst_base inst t = OK v /\ abi_decoder_vars_extend extras u v
Proof
  strip_tac >> drule_all abi_decoder_step_inputs_defined >> strip_tac >>
  drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
  drule_all abi_decoder_reentry_non_invoke >> strip_tac >>
  mp_tac (Q.SPECL [`abi_decoder_vars_extend extras`,
    `\s t. vsr_term_frame s = vsr_term_frame t`, `0`, `ARB`, `inst`, `s`, `t`]
    step_inst_preserves_R) >>
  impl_tac >- simp[abi_decoder_vars_extend_valid] >>
  asm_simp_tac (srw_ss()) [step_inst_non_invoke] >>
  Cases_on `step_inst_base inst t` >> simp[lift_result_def] >> metis_tac[]
QED

Theorem abi_decoder_sequence_vars_extend:
  !insts extras s t u.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  abi_decoder_vars_extend extras s t /\ run_inst_seq insts s = OK u ==>
  ?v. run_inst_seq insts t = OK v /\ abi_decoder_vars_extend extras u v
Proof
  Induct >- (simp[run_inst_seq_def] >> metis_tac[]) >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[] >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `abi_decoder_vars_extend extras u reached` >>
  qexists_tac `reached` >> simp[run_inst_seq_def]
QED
