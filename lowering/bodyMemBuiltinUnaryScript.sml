(* Memory case of the body induction (bodyMemory's body_mem_mutual): neg, abs
   and not on one operand. bodyExprClosureMemory's not/neg/abs cases
   (bodyNot*Memory, bodyNegMemory, bodyAbsMemory) predate the gas-counted
   expr_sim_mem and need porting; bodyNotMemoryProps builds. *)
Theory bodyMemBuiltinUnary
Ancestors
  bodyMemoryPreds

Theorem body_builtin_unary_mem_case:
  !cx ty bt e.
    (bt = Neg \/ bt = Abs \/ bt = Not) /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ty bt [e])
Proof
  cheat
QED
