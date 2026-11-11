(* Recursive statement memory composition. *)
Theory bodyStmtClosureMemory
Ancestors
  bodyExprStmtMemory bodyIfMemory bodySeqMemory
  bodyMemoryPreds bodyLiteralForceMemory

Theorem body_word_literal_stmts_mem_ok:
  !cx ann l. is_word_type ann ==> body_stmts_mem_ok cx [Expr (Literal ann l)]
Proof
  rpt strip_tac >> irule body_stmts_cons_mem_case >>
  simp[body_nil_mem_ok] >> irule body_expr_stmt_mem_case >>
  simp[body_literal_word_mem_case]
QED

