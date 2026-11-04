Theory lowerDloadCompletedOutput
Ancestors
  o1ContractLowerDloadTaint lowerDloadMacroBoundary lowerDloadPhaseBoundary
  ptrDiscipline venomExecSemantics venomState finite_map list

Theorem ld_load_completed_output_clean:
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u ==>
  FLOOKUP u.t_var out = SOME {}
Proof
  strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once ld_target_prefix_step_iff] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[SRULE [] (Q.INST [`n` |-> `2`] ld_target_prefix_step_iff)] >>
  strip_tac >>
  drule_all codecopy_mload_cleared >>
  disch_then (qspec_then `w'` assume_tac) >>
  `out_taint w d v = {}` by gvs[out_taint_def, ld_macro_operand_pc] >>
  simp[step_taint_def, set_var_taint_def, FLOOKUP_UPDATE]
QED
