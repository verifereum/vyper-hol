(* When the source fails before the constructor body (deploy_ctor_start has
 * no witness: the value transfer into a non-payable constructor, the
 * reentrancy lock), the unit's run is pointer-safe: the payable check, the
 * immutables region, the argument decode and the lock it runs before
 * failing touch only untainted bytes at or above imm_len, or the region by
 * its literal base.
 * TOP-LEVEL: deploy_ctor_prefix_fail_run_ptr_safe (admitted until proved).
 *)
Theory ctorDeployMemoryRunPtrPrefix
Ancestors
  ctorDeployLoweringDefs gasSummary ptrSafeRun ptrDiscipline venomInst

Theorem deploy_ctor_prefix_fail_run_ptr_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb cf fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. ptr_safe_blocks (deploy_dead tops runtime_bc am tx) (imm_len tops)
             fuel dunit.cu_context fn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  cheat
QED
