(* Memory case of the body induction (bodyMemory's body_mem_mutual): bare and
   unreachable assert; stmtAssertMemory's compile_assert_frag_mem is the
   fragment step. *)
Theory bodyMemAssert
Ancestors
  bodyMemoryPreds

Theorem body_assert_mem_case:
  !cx e ak.
    (ak = AssertBare \/ ak = AssertUnreachable) /\ body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (Assert e ak)
Proof
  cheat
QED
