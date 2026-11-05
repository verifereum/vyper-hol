(* The deployment unit's alloca frontier starts past the immutables fixed
 * region (deploy_entry_state), so every reachable frontier, plus LowerDload's
 * 32 bytes per DLOAD, is bounded by the region's size on top of the unit's
 * alloca budget; that sum stays below 2^256.
 * TOP-LEVEL: deploy_imm_budget_ok (admitted until run_deploy_lowering checks
 * the bound).
 *)
Theory ctorDeployImmBudget
Ancestors
  ctorDeployDefs vyperCompiler lowerDloadDefs

Theorem deploy_imm_budget_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan)
    ==>
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context < dimword (:256)
Proof
  cheat
QED
