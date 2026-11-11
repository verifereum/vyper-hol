(* Seam 2 joint induction, a family leaf of the stmt step: For. *)
Theory bodyIntCallFamStmtFor
Ancestors
  bodyIntCallFamStmtForRange bodyIntCallFamStmtForChecked
  bodyIntCallFamStmtForArray

Theorem intcall_for_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?x ty it n body. st = For x ty it n body) ==>
  intcall_stmts_producer fp [st]
Proof
  strip_tac >> gvs[] >>
  rename1 `For x ty it n bd` >>
  `intcall_stmts_producer fp bd` by
    (first_x_assum irule >> simp[intcall_for_body_size]) >>
  Cases_on `it`
  >- (irule intcall_stmts_producer_for_array >> simp[]) >>
  rename1 `Range e1 e2` >>
  Cases_on `?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)`
  >- (gvs[] >> irule intcall_stmts_producer_for_range_lit >> simp[]) >>
  irule intcall_stmts_producer_for_range_checked >> fs[]
QED
