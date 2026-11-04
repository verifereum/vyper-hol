Theory lowerDloadPtrClosure
Ancestors
  pointerConfinedDefs venomInst o1PassContract list pred_set While

Theorem pointer_use_step_member:
  MEM y (pointer_use_step fn xs) <=>
  ?i v. MEM i (fn_insts fn) /\
        is_pointer_preserving_op i.inst_opcode /\
        MEM (Var v) i.inst_operands /\ MEM v xs /\ MEM y i.inst_outputs
Proof
  simp[pointer_use_step_def, fn_insts_def, fn_insts_blocks_MEM,
       MEM_FLAT, MEM_MAP, EXISTS_MEM, PULL_EXISTS] >>
  eq_tac >> rpt strip_tac >> gvs[COND_RAND, COND_RATOR, AllCaseEqs()]
  >- (Cases_on `op` >> gvs[] >> metis_tac[]) >>
  qexistsl [`bb`,`i`] >> simp[] >> qexists_tac `Var v` >> simp[]
QED
