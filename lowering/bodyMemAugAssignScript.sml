(* Memory case of the body induction (bodyMemory's body_mem_mutual): augmented
   assignment. *)
Theory bodyMemAugAssign
Ancestors
  bodyMemoryPreds

Theorem body_augassign_mem_case:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\ body_base_target_mem_ok cx t ==>
    body_stmt_mem_ok cx (AugAssign ty t bop e)
Proof
  cheat
QED
