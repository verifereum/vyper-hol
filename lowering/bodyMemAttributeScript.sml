(* Memory case of the body induction (bodyMemory's body_mem_mutual): a field
   read. bodyExprClosureMemory's body_attribute_name_mem_case (a field of a
   local struct, through bodyFieldMemoryProps) predates the gas-counted
   expr_sim_mem and needs porting; other bases have no case yet. *)
Theory bodyMemAttribute
Ancestors
  bodyMemoryPreds

Theorem body_attribute_mem_ok:
  !cx v9 e id. body_expr_mem_ok cx e ==> body_expr_mem_ok cx (Attribute v9 e id)
Proof
  cheat
QED
