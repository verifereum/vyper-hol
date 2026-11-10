(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   selfdestruct.  It holds vacuously: selfdestruct is an EVM-run root
   (expr_evm_run_root), which expr_body_pre excludes. *)
Theory bodyMemSelfDestruct
Ancestors
  bodyMemoryPreds

Theorem body_selfdestruct_mem_case:
  !cx v24 es v25.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  rw[body_expr_mem_ok_def, exprSimHypsDefsTheory.expr_body_pre_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.expr_evm_run_root_def]
QED
