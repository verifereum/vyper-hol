(* Seam 2 joint induction, a family leaf of the stmt step: Raise and Assert. *)
Theory bodyIntCallFamStmtExit
Ancestors
  supportedStmts bodyIntCallFamStmtExitAssert bodyIntCallJointContract bodyIntCallFamStmtExitReason bodyIntCallFamStmtExitLiteral bodyIntCallFamStmtExitBoundary bodyIntCallFamStmtExitRaise

Theorem intcall_exit_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  ((?r. st = Raise r) \/ (?e r. st = Assert e r)) ==>
  intcall_stmts_producer fp [st]
Proof
  strip_tac >> gvs[]
  >- (Cases_on `r`
      >- simp[bodyIntCallJointStmtRaiseTheory.intcall_stmts_producer_raise]
      >- simp[bodyIntCallJointStmtRaiseTheory.intcall_stmts_producer_raise]
      >- (irule intcall_stmts_producer_raise_reason >> simp[]) >>
      simp[intcall_stmts_producer_def, supported_stmts_list,
           supported_stmt_def, supported_raise_reason_def]) >>
  Cases_on `r`
  >- (irule bodyIntCallJointStmtAssertTheory.intcall_stmts_producer_assert >> simp[])
  >- (irule bodyIntCallJointStmtAssertTheory.intcall_stmts_producer_assert >> simp[])
  >- (irule intcall_stmts_producer_assert_reason >> simp[] >>
      irule intcall_stmts_producer_raise_reason >> simp[]) >>
  simp[intcall_stmts_producer_def, supported_stmts_list,
       supported_stmt_def, supported_assert_reason_def]
QED
