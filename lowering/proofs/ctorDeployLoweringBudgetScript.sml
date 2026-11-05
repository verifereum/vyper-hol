(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until run_deploy_lowering checks the bound: the same statement as
   deploy_imm_budget_ok in ctorDeployImmBudget, widened by the runtime code's
   length, which the constructor epilogue returns ahead of the immutables. *)
Theory ctorDeployLoweringBudget
Ancestors
  ctorDeployDefs vyperCompiler lowerDloadDefs

Theorem deploy_imm_budget_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan)
    ==>
    LENGTH runtime_bc + imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context < dimword (:256)
Proof
  cheat
QED
