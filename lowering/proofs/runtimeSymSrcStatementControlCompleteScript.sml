Theory runtimeSymSrcStatementControlComplete
Ancestors
  runtimeSymSrcStatementControl runtimeSymSrcStatementRange
  runtimeSymSrcStatementArray runtimeSymSrcIterCopy runtimeSymSrcDeclarations
  runtimeSymSrcInterfaces stmtLowering exprLowering vyperAST

(* Control-family join: the iter-copy and local-declaration obligations of
   the conditional array theorem are discharged here. Expression and proper
   body callbacks remain available to the outer mutual statement induction.
   supported_stmt and compile_stmt cover the same statement constructors;
   the compiler catch-all adds only the NoLoop Break/Continue cases, already
   handled by runtime_sym_stmt_break and runtime_sym_stmt_continue. *)
Theorem runtime_sym_stmt_for_array:
  runtime_sym_expr_contract tops compile_expr ce (expr_type arr_e) arr_e /\
  (!bs ce' lc'. runtime_sym_stmts_contract tops bs compile_stmts ce' lc' ty loop_body) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty
    (For id fty (Array arr_e) bound loop_body)
Proof
  strip_tac >> irule runtime_sym_stmt_for_array_conditional >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all runtime_sym_emit_local_alloca >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all runtime_sym_declare_local >> simp[]) >>
  rpt strip_tac >> drule_all runtime_sym_iter_elem_copy >> simp[]
QED
