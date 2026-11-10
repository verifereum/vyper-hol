(* Allocation frames used by nested-call argument initialization. *)
Theory bodyIntCallFamCallIntEntryAllocationBoundary
Ancestors
  bodyIntCallFamCallIntStageAllocation loweringPosts

Theorem intcall_allocation_old_regions:
  stmt_state_rel ctx func ce cx es u /\
  FLOOKUP u.vs_allocas site = SOME (dst,cap) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) ==>
  !aid lb len. aid < site /\ FLOOKUP s.vs_allocas aid = SOME (lb,len) ==>
    regions_disjoint lb len dst cap
Proof
  rpt strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (lb,len)` by metis_tac[] >>
  `aid <> site` by decide_tac >>
  metis_tac[exprSimPrecompilesTheory.state_allocations_disjoint]
QED

Theorem intcall_expr_val_rel_same_memory:
  expr_val_rel cx ty v op s /\
  eval_operand op u = eval_operand op s /\ u.vs_memory = s.vs_memory ==>
  expr_val_rel cx ty v op u
Proof
  simp[expr_val_rel_def]
QED

Theorem intcall_regions_disjoint_subwindow:
  regions_disjoint p k off len /\ off <= dst /\ dst + cap <= off + len ==>
  regions_disjoint p k dst cap
Proof
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED
