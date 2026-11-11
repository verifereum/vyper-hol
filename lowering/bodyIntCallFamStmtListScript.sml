(* Seam 2 joint induction, the list case of the statement step: a list
   from its statements. *)
Theory bodyIntCallFamStmtList
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtZero bodyIntCallJointStmtSeq

Theorem intcall_stmts_list_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) ==>
  !ss. (!st. MEM st ss ==> intcall_stmts_producer fp [st]) ==>
       intcall_stmts_producer fp ss
Proof
  strip_tac >> Induct >> rw[intcall_stmts_producer_nil] >>
  irule intcall_stmts_producer_cons >> simp[]
QED
