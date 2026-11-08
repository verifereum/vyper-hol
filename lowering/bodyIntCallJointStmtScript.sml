(* Seam 2 joint induction step: statements and statement lists. *)
Theory bodyIntCallJointStmt
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtList bodyIntCallFamStmtSimple
  bodyIntCallFamStmtExit bodyIntCallFamStmtMutation bodyIntCallFamStmtReturn
  bodyIntCallFamStmtIf bodyIntCallFamStmtFor

(* L-stmt (C1.3.16): a single statement (the list [st]) of any form, given
   the producers of every expression and of every smaller statement list
   (If and For bodies), and a list from its statements. *)
Theorem intcall_stmt_producer_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) ==>
  (!st. (!ss. list_size stmt_size ss < stmt_size st ==>
              intcall_stmts_producer fp ss) ==>
        intcall_stmts_producer fp [st]) /\
  (!ss. (!st. MEM st ss ==> intcall_stmts_producer fp [st]) ==>
        intcall_stmts_producer fp ss)
Proof
  strip_tac >> conj_tac
  >- (Cases_on `st` >> strip_tac
      >~ [`For _ _ _ _ _`] >- (irule intcall_for_stmt_step >> metis_tac[])
      >~ [`If _ _ _`] >- (irule intcall_if_stmt_step >> metis_tac[])
      >~ [`Return _`] >- (irule intcall_return_stmt_step >> metis_tac[])
      >~ [`Raise _`] >- (irule intcall_exit_stmt_step >> metis_tac[])
      >~ [`Assert _ _`] >- (irule intcall_exit_stmt_step >> metis_tac[])
      >~ [`Log _ _`] >- (irule intcall_exit_stmt_step >> metis_tac[])
      >~ [`Assign _ _`] >- (irule intcall_mutation_stmt_step >> metis_tac[])
      >~ [`AugAssign _ _ _ _`] >- (irule intcall_mutation_stmt_step >> metis_tac[])
      >~ [`Append _ _`] >- (irule intcall_mutation_stmt_step >> metis_tac[])
      >~ [`AnnAssign _ _ _`] >- (irule intcall_mutation_stmt_step >> metis_tac[])
      >> irule intcall_simple_stmt_step >> metis_tac[]) >>
  rpt strip_tac >> irule intcall_stmts_list_step >> metis_tac[]
QED
