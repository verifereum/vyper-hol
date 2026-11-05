(* The raw deployment unit's run is memory-safe: every instruction it
 * executes, callee frames included, reads and writes memory below the
 * allocation frontier (or is a revert forwarding).  The deploy twin of
 * lower_vyper_runtime_unit_run_mem_safe: the constructor prefix (call value
 * check, immutables region, argument decode, lock), the body, the exit and
 * epilogue, and the constructor's internal functions.
 * TOP-LEVEL: deploy_unit_run_mem_safe (admitted until proved).
 *)
Theory ctorDeployMemoryRunMem
Ancestors
  ctorDeployDefs gasSummary memSafeRun venomInst

Theorem deploy_unit_run_mem_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. mem_safe_blocks fuel dunit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  cheat
QED
