(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringNoCtor
Ancestors
  ctorDeployLoweringDefs ctorDeployLoweringBudget o1PassContract gasSummary

(* Without a constructor, load_contract runs the synthetic empty one, and the
   unit is compile_simple_deploy's. *)
Theorem deploy_no_ctor_correct:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs exts ints fb.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, NONE)
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
