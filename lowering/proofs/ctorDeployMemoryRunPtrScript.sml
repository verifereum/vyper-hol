(* The raw deployment unit's run is pointer-safe, with its taint confined to
 * deploy_dead's bytes and its accesses below imm_len exempt (the immutables
 * fixed region, addressed by literal offsets).  The deploy twin of
 * lower_vyper_runtime_unit_run_ptr_safe_composed, at PG = [] (__deploy has
 * no parameters).
 * TOP-LEVEL: deploy_unit_run_ptr_safe (admitted until proved).
 *)
Theory ctorDeployMemoryRunPtr
Ancestors
  ctorDeployDefs gasSummary ptrSafeRun ptrDiscipline venomInst

Theorem deploy_unit_run_ptr_safe:
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
    !fuel. ptr_safe_blocks (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel dunit.cu_context fn
             [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  cheat
QED
