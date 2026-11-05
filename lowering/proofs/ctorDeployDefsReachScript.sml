(* Definitions reach uses in the raw deployment unit (the deploy counterpart of
 * lower_vyper_runtime_unit_defs_reach_uses).
 * TOP-LEVEL: deploy_unit_defs_reach_uses (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployDefsReach
Ancestors
  ctorDeployDefs o1PassContract

Theorem deploy_unit_defs_reach_uses:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx
    ==>
    unit_defs_reach_uses dunit
Proof
  cheat
QED
