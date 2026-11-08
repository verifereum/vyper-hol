(* Seam 2 joint induction step: statements and statement lists. *)
Theory bodyIntCallJointStmt
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtBoundary bodyIntCallJointStmtZero bodyIntCallJointStmtSeq bodyIntCallJointStmtExpr

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
  cheat
QED
