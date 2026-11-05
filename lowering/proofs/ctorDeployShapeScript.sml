(* Structural producers on the raw deployment unit that run_venom_pipeline_correct
 * consumes (the deploy counterparts of lower_vyper_runtime_unit_source_unit_ok,
 * _o1_shape_extras, _global_reserved and the eom/fixed-region facts).
 * TOP-LEVEL: deploy_unit_shape_ok (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployShape
Ancestors
  ctorDeployDefs o1PassContract unitShapeDefs staticLayoutDefs

Theorem deploy_unit_shape_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx
    ==>
    o1_source_unit_ok dunit /\ unit_entry_no_params dunit /\
    unit_fmp_unsealed dunit /\
    EVERY (\fn. fn.fn_eom = NONE) dunit.cu_context.ctx_functions /\
    fixed_region_reserved 0 dunit.cu_context /\
    reserved_intervals_wf dunit.cu_context.ctx_global_reserved
Proof
  cheat
QED
