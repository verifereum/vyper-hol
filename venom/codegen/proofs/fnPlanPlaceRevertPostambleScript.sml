Theory fnPlanPlaceRevertPostamble
Ancestors
  codegen asmSem symbolResolve planExec stackPlanGen list

Theorem distinct_symbols_no_later_write:
  !prog i lbl.
    ALL_DISTINCT (FLAT (MAP asm_defined_symbols prog)) /\
    i < LENGTH prog /\ EL i prog = AsmLabel lbl ==>
    !j. i < j /\ j < LENGTH prog ==>
      EL j prog <> AsmLabel lbl /\
      (!l. EL j prog = AsmDataHeader l ==> l <> lbl)
Proof
  Induct_on `prog` >- simp[] >>
  rpt gen_tac >> Cases_on `i`
  >- (simp[] >> strip_tac >> gvs[asm_defined_symbols_def] >>
      Cases_on `j` >- simp[] >>
      simp[] >> strip_tac >>
      `MEM (EL n prog) prog` by (simp[MEM_EL] >> metis_tac[]) >>
      gvs[MEM_FLAT, MEM_MAP] >>
      metis_tac[asm_defined_symbols_def, MEM]) >>
  simp[] >> strip_tac >> Cases_on `j` >- simp[] >>
  simp[] >> strip_tac >> gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[arithmeticTheory.LESS_TRANS]
QED
