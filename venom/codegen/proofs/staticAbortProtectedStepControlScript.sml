Theory staticAbortProtectedStepControl
Ancestors
  asmSymPc asmSymPcOwn asmSymSem asmSymOwnCode asmSplice asmOptimizer asmSem list

Theorem protected_sym_step_control:
  sym_step p env inst u = SymOK v ==>
  (v.sym_base.as_pc = u.sym_base.as_pc + 1 /\ ~asm_terminal_op inst) \/
  (v.sym_base.as_pc < LENGTH p /\
   ?l. EL v.sym_base.as_pc p = AsmLabel l)
Proof
  strip_tac >>
  Cases_on `inst = AsmOp "JUMP"`
  >- (gvs[sym_step_def, sym_step_op_def, sym_jump_def, AllCaseEqs()] >>
      Cases_on `dest` >> gvs[sym_jump_dest_def, AllCaseEqs()] >>
      gvs[INDEX_OF_eq_SOME] >> metis_tac[]) >>
  Cases_on `inst = AsmOp "JUMPI"`
  >- (gvs[sym_step_def, sym_step_op_def, sym_jumpi_def, AllCaseEqs()] >>
      TRY (drule sym_set_stack_pc_next >>
           simp[asm_terminal_op_def] >> NO_TAC) >>
      Cases_on `dest` >>
      gvs[sym_jump_dest_def, AllCaseEqs(), INDEX_OF_eq_SOME] >>
      metis_tac[]) >>
  Cases_on `asm_terminal_op inst`
  >- (gvs[asm_terminal_op_def, sym_step_def, sym_step_op_def,
          dup_table_def, swap_table_def, sym_step_concrete_def,
          AllCaseEqs()] >>
      drule sym_lift_ok >> strip_tac >>
      gvs[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
          asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
          asm_return_op_def, asm_revert_op_def, AllCaseEqs()]) >>
  disj1_tac >> simp[] >> metis_tac[sym_step_pc_next]
QED

Theorem protected_sym_step_control_mode:
  (if allow_own then sym_step_own p env own inst u else sym_step p env inst u) =
    SymOK v ==>
  (v.sym_base.as_pc = u.sym_base.as_pc + 1 /\ ~asm_terminal_op inst) \/
  (v.sym_base.as_pc < LENGTH p /\
   ?l. EL v.sym_base.as_pc p = AsmLabel l)
Proof
  Cases_on `allow_own` >> simp[] >> strip_tac
  >- (Cases_on `inst = AsmOp "CODESIZE" \/ inst = AsmOp "CODECOPY"`
      >- (disj1_tac >> fs[asm_terminal_op_def] >>
          drule_at (Pat `sym_step_own _ _ _ _ _ = _`) sym_step_own_pc_next >>
          simp[]) >>
      fs[sym_step_own_eq] >> metis_tac[protected_sym_step_control]) >>
  metis_tac[protected_sym_step_control]
QED
