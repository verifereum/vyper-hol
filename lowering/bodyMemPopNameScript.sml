(* Memory case of the body induction (bodyMemory's body_mem_mutual): pop on a
   local or a module variable. *)
Theory bodyMemPopName
Ancestors
  bodyMemoryPreds bodyMemPopLocal bodyMemPopToplevel

Theorem body_pop_name_mem_case:
  !cx ann bt.
    (?id. bt = NameTarget id) \/ (?nid. bt = TopLevelNameTarget nid) ==>
    body_expr_mem_ok cx (Pop ann bt)
Proof
  rpt strip_tac >> gvs[body_pop_local_mem, body_pop_toplevel_mem]
QED
