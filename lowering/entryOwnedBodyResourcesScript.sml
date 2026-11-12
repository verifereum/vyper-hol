(* Allocation room at the fixed actual registration endpoint. *)
Theory entryOwnedBodyResources
Ancestors entryInitialResources entryPrefixAllocationResources

Theorem runtime_owned_endpoint_alloca_room:
  lower_vyper_runtime_unit tops pol = SOME unit /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  alloca_frontier_inv unit.cu_context func site out ==>
  alloca_room unit.cu_context func out
Proof
  strip_tac >> drule_all runtime_entry_allocation_code_resources >>
  strip_tac >> irule alloca_frontier_inv_room >> simp[] >> qexists_tac `site` >> simp[]
QED
