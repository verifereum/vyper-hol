(* Without a constructor, the deploy unit is compile_simple_deploy's: an
 * ALLOCA for the runtime code and the immutables section, a CODECOPY into
 * it and a RETURN of it.  Its run is memory-safe.
 * TOP-LEVEL: deploy_no_ctor_run_mem_safe (admitted until proved).
 *)
Theory ctorDeployMemoryRunMemNoCtor
Ancestors
  ctorDeployDefs gasSummary memSafeRun venomInst

Theorem deploy_no_ctor_run_mem_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    classify_functions tops = (exts, ints, fb, NONE) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. mem_safe_blocks fuel dunit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  cheat
QED
