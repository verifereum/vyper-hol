(* Definitions reach uses in the raw deployment unit (the deploy counterpart of
 * lower_vyper_runtime_unit_defs_reach_uses).
 * TOP-LEVEL: deploy_unit_defs_reach_uses (a piece of e2e_deploy_correctness).
 * run_deploy_lowering decides it on the unit (lowering_context_ok).
 *)
Theory ctorDeployDefsReach
Ancestors
  ctorDeployDefs o1PassContract deployUnitProducers vyperCompiler

Theorem deploy_unit_defs_reach_uses:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx
    ==>
    unit_defs_reach_uses dunit
Proof
  rpt gen_tac >> simp[deploy_phases_def] >> strip_tac >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule lowering_context_ok_defs_reach_uses >>
  simp[unit_defs_reach_uses_def]
QED
