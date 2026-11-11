(* The constructor prefix with memory: the run from the unit's entry, after
 * the payable check, the immutables region, the constructor arguments'
 * decode (DLOAD from the data section) and the lock, reaches the body start
 * sa in a state s0 related to the source's body start, with its allocation
 * history and the GAS readings still unread; and a memory-safe run from s0
 * makes the run from the entry memory-safe.  The constructor's frame has no
 * caller return buffer.
 * TOP-LEVEL: deploy_ctor_entry_run_mem (admitted until proved).
 *)
Theory ctorDeployMemoryRunMemEntry
Ancestors
  ctorDeployLoweringDefs o1PassContract stmtSimDefs gasSummary memSafeRun
  allocaHistory venomInst

Theorem deploy_ctor_entry_run_mem:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func
   mut am_c es0 fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    cenv.ce_return_buf = NONE /\
    ?s0.
      stmt_state_rel dunit.cu_context func cenv
        (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
      alloca_history func s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      ((!fuel. mem_safe_run fuel dunit.cu_context func s0) ==>
    !fuel. mem_safe_blocks fuel dunit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>))
Proof
  cheat
QED
