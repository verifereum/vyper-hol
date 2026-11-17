(* Allocation-origin boundaries for same-endpoint canonical decoding. *)
Theory ctorDeployMemoryRunPtrPrefixAllocationFloor
Ancestors
  actualAllocExec ptrDiscipline venomState venomExecSemantics
  finite_map arithmetic

Theorem prefix_allocation_floor_frame:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >> fs[allocas_from_def] >> metis_tac[]
QED
