(* Completed block history is preserved by recursive compiler consumers. *)
Theory bodyIntCallPrefix
Ancestors
  exprLoweringProps stmtLoweringMono fragExec moduleLowering

Theorem compile_expr_cs_appends:
  cs_appends (compile_expr ce ty e)
Proof
  rw[cs_appends_def] >> drule (cj 1 compile_expr_grows) >> simp[]
QED

Theorem lower_value_compile_expr_cs_appends:
  cs_appends (lower_value compile_expr ce ty e)
Proof
  rw[cs_appends_def] >> drule (cj 2 compile_expr_grows) >> simp[]
QED

Theorem cs_mono_cs_appends:
  cs_mono m ==> cs_appends m
Proof
  simp[cs_mono_def, cs_appends_def] >> metis_tac[]
QED

Theorem compile_stmt_cs_appends:
  cs_appends (compile_stmt ce lc ty s)
Proof
  irule cs_mono_cs_appends >> simp[cj 1 compile_stmt_cs_mono]
QED

Theorem compile_stmts_cs_appends:
  cs_appends (compile_stmts ce lc ty ss)
Proof
  irule cs_mono_cs_appends >> simp[cj 2 compile_stmt_cs_mono]
QED

Theorem intcall_appends_check[local]:
  cs_appends (compile_expr ce ty (Call ann (IntCall fid) args dflt))
Proof
  simp[compile_expr_cs_appends]
QED

Theorem external_return_appends_check[local]:
  ce.ce_return_pc = NONE ==>
  cs_appends (compile_stmt ce lc ty (Return (SOME e)))
Proof
  simp[compile_stmt_cs_appends]
QED
