Theory concretizePtrActualWrites
Ancestors ptrDiscipline memLocDefs codegenRel concretizeMemLocDefs

Theorem ptr_exact_size_step_writes:
  inst_write_size inst = SOME n ==>
  step_writes inst s post = source_memory_write_ranges inst s
Proof
  Cases_on `inst.inst_opcode = CALL` >-
    (simp[inst_write_size_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = STATICCALL` >-
    (simp[inst_write_size_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = DELEGATECALL` >-
    (simp[inst_write_size_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  simp[step_writes_def]
QED
