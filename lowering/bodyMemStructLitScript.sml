(* Memory case of the body induction (bodyMemory's body_mem_mutual): struct
   literal. *)
Theory bodyMemStructLit
Ancestors
  bodyMemoryPreds

Theorem body_structlit_mem_case:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_mem_ok cx (MAP SND kes)) ==>
    body_expr_mem_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  cheat
QED
