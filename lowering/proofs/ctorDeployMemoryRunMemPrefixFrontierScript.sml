(* Consumer bounds for the deployment's immutables-raised frontier. *)
Theory ctorDeployMemoryRunMemPrefixFrontier
Ancestors
  ctorDeployMemoryFrontier ctorDeployDefs o1PassContract
  allocaFrontierBound allocaBudgetProps arithmetic words

Theorem ctor_prefix_frontier_bound:
  alloca_frontier_inv_from k ctx fn inst s ==>
  s.vs_alloca_next <= k + unit_alloca_budget ctx
Proof
  simp[alloca_frontier_inv_from_def] >> rpt strip_tac >> decide_tac
QED

Theorem ctor_prefix_frontier_headroom:
  alloca_frontier_inv_from k ctx fn inst s /\
  k + unit_alloca_budget ctx + reserve < dimword (:256) ==>
  s.vs_alloca_next + reserve < dimword (:256)
Proof
  strip_tac >> drule ctor_prefix_frontier_bound >> decide_tac
QED

Theorem ctor_prefix_entry_frontier:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn ==>
  fn_entry_inv (alloca_frontier_inv_from (imm_len tops))
    dunit.cu_context fn vs
Proof
  strip_tac >> drule_all deploy_unit_run_entry >> strip_tac >> gvs[] >>
  drule_all lowered_unit_entry_facts >> strip_tac >>
  irule alloca_frontier_inv_from_entry >> simp[] >> metis_tac[]
QED
