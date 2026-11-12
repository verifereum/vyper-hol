Theory bodyPtrStructLitOwnershipEnvironment
Ancestors stmtLowering compileEnv

Theorem declare_local_alloca_mode:
  declare_local ce id ty st = (ce',st') ==>
  ce'.ce_alloca_locals = ce.ce_alloca_locals
Proof
  Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def] >>
  strip_tac >> gvs[]
QED

Theorem declare_stmt_local_alloca_mode:
  declare_stmt_local ce s st = (ce',st') ==>
  ce'.ce_alloca_locals = ce.ce_alloca_locals
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, comp_return_def] >>
  metis_tac[declare_local_alloca_mode]
QED
