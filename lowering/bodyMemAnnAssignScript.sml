(* Memory case of the body induction (bodyMemory's body_mem_mutual): annotated
   assignment (declaration); bodyDeclMemory has the store steps. *)
Theory bodyMemAnnAssign
Ancestors
  bodyMemoryPreds

Theorem body_annassign_mem_case:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_mem_ok cx e) ==>
    body_stmt_mem_ok cx (AnnAssign id typ e)
Proof
  cheat
QED
