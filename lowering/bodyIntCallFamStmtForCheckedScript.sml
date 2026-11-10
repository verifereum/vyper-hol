(* Seam 2 joint induction, For family: a Range whose endpoints are not both
   integer literals, compiled with the checked range prefix. *)
Theory bodyIntCallFamStmtForChecked
Ancestors
  bodyIntCallFamStmtForRange

Theorem intcall_stmts_producer_for_range_checked:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  intcall_stmts_producer fp stmts /\
  ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) ==>
  intcall_stmts_producer fp [For id fty (Range e1 e2) bound stmts]
Proof
  cheat
QED
