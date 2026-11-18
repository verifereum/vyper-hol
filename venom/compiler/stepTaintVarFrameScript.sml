Theory stepTaintVarFrame
Ancestors
  ptrDiscipline venomInst finite_map list

Theorem step_taint_other_var:
  ~MEM x i.inst_outputs ==>
  FLOOKUP (step_taint i s t tn).t_var x = FLOOKUP tn.t_var x
Proof
  simp[step_taint_def, set_var_taint_def] >>
  Cases_on `i.inst_outputs` >> simp[FLOOKUP_DRESTRICT] >>
  rename1 `i.inst_outputs = h::outs` >>
  Cases_on `outs` >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
