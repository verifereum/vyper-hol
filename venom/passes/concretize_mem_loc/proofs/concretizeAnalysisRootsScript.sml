Theory concretizeAnalysisRoots
Ancestors pointerClosure ptrDiscipline pointerConfinedDefs list pred_set venomInst

Theorem ptr_roots_output_bound:
  ptr_roots P fn SUBSET
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))
Proof
  rw[SUBSET_DEF, ptr_roots_def, alloca_roots_def] >>
  gvs[inst_output_def, AllCaseEqs()] >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[MEM]
QED

Theorem ptr_roots_finite:
  FINITE (ptr_roots P fn)
Proof
  irule SUBSET_FINITE >>
  qexists `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  simp[ptr_roots_output_bound]
QED
