(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringEntry
Ancestors
  ctorDeployLoweringDefs o1PassContract stmtSimDefs ctorDeployLoweringEntryFmp

(* The run from the unit's entry, after the payable check, the immutables
   region, the constructor arguments' registration and the lock, reaches
   the body start sa in a state s0 related to the source's body start
   (with the run's call outcomes, which the call-free body never reads),
   with the GAS readings still unread; every result from s0 is a result of
   run_context.  The source and the unit select the same constructor. *)
Theorem deploy_ctor_entry_reaches_body:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut nr' body' am_c es0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0) ==>
    nr' = nr /\ body' = body /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    ?s0.
      stmt_state_rel dunit.cu_context func cenv (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      !fuel r. run_from fuel dunit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' dunit.cu_context vs = r
Proof
  cheat
QED
