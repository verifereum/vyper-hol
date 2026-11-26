(* Classify aborts of the straight scalar conversion suffix. *)
Theory bodyConvertScalarAbortKind
Ancestors
  freshWrites exprLoweringProps venomExecSemantics venomInst venomState list
  opcodeClass[qualified]

Theorem fresh_step_no_exhalt[local]:
  fresh_write_op i.inst_opcode /\ i.inst_opcode <> ASSERT_UNREACHABLE ==>
  step_inst_base i s <> Abort ExHalt_abort u
Proof
  simp[fresh_write_op_def] >> strip_tac >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[opcodeClassTheory.exec_result_helpers_no_halt_abort, AllCaseEqs()]
QED

Theorem fresh_run_abort_revert:
  EVERY (\i. fresh_write_op i.inst_opcode) code /\
  EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) code /\
  run_inst_seq code s = Abort a u ==> a = Revert_abort
Proof
  qid_spec_tac `s` >> Induct_on `code` >> simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[]
  >- metis_tac[] >>
  Cases_on `a` >> gvs[] >> metis_tac[fresh_step_no_exhalt]
QED
