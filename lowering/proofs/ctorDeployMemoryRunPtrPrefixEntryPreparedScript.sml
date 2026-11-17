Theory ctorDeployMemoryRunPtrPrefixEntryPrepared
Ancestors
  ctorDeployMemoryRunPtrPrefixEntryRegisterList ctorDeployMemoryRunPtrDefs
  ctorDeployMemoryFrontier e2eDeployDefs

Theorem prefix_entry_frontier_all_sites:
  alloca_frontier_inv_from k ctx func site s ==>
  !site'. alloca_frontier_inv_from k ctx func site' s
Proof
  simp[alloca_frontier_inv_from_def]
QED
