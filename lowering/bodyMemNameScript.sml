(* Memory case of the body induction (bodyMemory's body_mem_mutual): a local
   name. bodyNameWordMemory's word-value case builds; bodyNameNonwordMemory's
   non-word case (and bodyNameMemory, which combines them) predates the gas-
   counted expr_sim_mem and needs porting; words that are not word values
   (bytesM, address) have no case yet. *)
Theory bodyMemName
Ancestors
  bodyMemoryPreds

Theorem body_name_mem_ok:
  !cx ann id. body_expr_mem_ok cx (Name ann id)
Proof
  cheat
QED
