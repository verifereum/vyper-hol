(* Memory case of the body induction (bodyMemory's body_mem_mutual): a module
   variable or immutable. bodyToplevelWordMemory's word case and
   bodyToplevelAggregateMemory's immutable case predate the gas-counted
   expr_sim_mem (they fail in bodyEnvMemory and bodyFieldMemoryProps) and need
   porting; non-word storage variables have no case yet. *)
Theory bodyMemToplevel
Ancestors
  bodyMemoryPreds

Theorem body_toplevel_mem_ok:
  !cx ann src id. body_expr_mem_ok cx (TopLevelName ann (src,id))
Proof
  cheat
QED
