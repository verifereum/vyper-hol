Theory concretizePtrKillBoundary
Ancestors
  concretizePtrReadCoverage concretizeMemLocDefs memLocDefs
  ptrDiscipline codegenRel venomExecSemantics venomState

Theorem ptr_literal_write_range_size:
  !inst s n off len.
    inst_write_size inst = SOME n /\
    MEM (off,len) (source_memory_write_ranges inst s) ==> len = n
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode` >>
  simp[inst_write_size_def, mem_write_ops_def,
       source_memory_write_ranges_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), fixed_source_write_range_def,
      sized_source_write_range_def] >>
  gvs[eval_operand_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
  qpat_x_assum `MEM _ _` mp_tac >>
  Cases_on `eval_operand dst s` >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED
