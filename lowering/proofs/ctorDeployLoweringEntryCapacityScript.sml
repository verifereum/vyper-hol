(* Deployment reserves immutables before any ALLOCA site. *)
Theory ctorDeployLoweringEntryCapacity
Ancestors
  ctorDeployMemoryFrontier ctorDeployLoweringBudget
  words

Theorem deploy_ctor_offset_frontier_bound:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan fn site s.
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  alloca_frontier_inv_from (imm_len tops) dunit.cu_context fn site s ==>
  s.vs_alloca_next < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_imm_budget_ok >>
  qpat_x_assum `alloca_frontier_inv_from _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[alloca_frontier_inv_from_def] >>
  rpt strip_tac >> decide_tac
QED
