(* Constructor lowering correctness (deploy S1): load_contract against a run of
 * the raw deployment unit from the creation frame's entry state, up to the
 * gas readings the O1 pipeline may vary. The source reads msg.gas from the
 * readings the Venom run consumes (gas_explicit marks vs.vs_gas_readings).
 * TOP-LEVEL: deploy_unit_execution_correct (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployLowering
Ancestors
  ctorDeployDefs o1PassContract gasSummary

Theorem deploy_unit_execution_correct:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es)
    ==>
    ?marks.
      deploy_source_exempt tops
        (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
           [(NONE, tops)] []) \/
      ?fuel. deploy_venom_result_rel tops runtime_bc tx
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])
               (run_context fuel dunit.cu_context vs)
Proof
  cheat
QED
