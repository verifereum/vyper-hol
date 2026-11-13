Theory runtimeSymSrcStatements
Ancestors
  runtimeSymSrcStatementAssignFamily runtimeSymSrcStatementExits
  runtimeSymSrcStatementControlComplete runtimeSymSrcContextComplete
  runtimeSymSrcOpenValues runtimeSymSrcBinops runtimeSymSrcModuleBodies
  runtimeSymSrcLiteralEnv runtimeSymSrcDeclarations supportedStmts
  runtimeSymSrcInterfaces stmtLowering compileEnv supportedStmtTraverse vyperAST

Theorem runtime_sym_stmts_nil:
  runtime_sym_stmts_contract tops bs compile_stmts ce lc ty []
Proof
  simp[runtime_sym_stmts_contract_def, compile_stmt_def, comp_return_def]
QED

Theorem runtime_sym_stmts_cons:
  (!ce. runtime_sym_stmt_contract tops bs compile_stmt ce lc ty stmt) /\
  (!ce. runtime_sym_stmts_contract tops bs compile_stmts ce lc ty stmts) ==>
  runtime_sym_stmts_contract tops bs compile_stmts ce lc ty (stmt::stmts)
Proof
  simp[runtime_sym_stmts_contract_def, runtime_sym_stmt_contract_def] >>
  rpt strip_tac >>
  gvs[Once compile_stmt_def, comp_get_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  Cases_on `block_is_terminated s` >>
  gvs[comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all runtime_sym_declare_stmt_local >> strip_tac >>
  fs[supported_stmt_def, supported_stmt_expr_exists_def] >>
  metis_tac[]
QED

