(* Memory safety of the raw deployment unit (the deploy counterpart of
 * lower_vyper_runtime_unit_memory_ok), with no dead bytes.
 * TOP-LEVEL: deploy_unit_memory_ok (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployMemory
Ancestors
  ctorDeployDefs o1PassContract gasSummary unitTransformDefs ptrDiscipline

Theorem deploy_unit_memory_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (entry_venom_state prog cplan es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] []))
    ==>
    raw_unit_memory_ok dunit.cu_context vs /\
    ptr_discipline 0 dunit.cu_context vs /\
    taint_within deploy_dead dunit.cu_context vs
Proof
  cheat
QED
