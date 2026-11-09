(* The constructor body with the pointer ghost, in the deployment's dead
 * bytes and bound: from the body start s0 with deploy_ptr_inv, given that
 * every return's exit block (unlock and epilogue) halts pointer-safely, the
 * body either falls off its end at sb with deploy_ptr_inv, pointer safety
 * from there giving it from s0, or exits pointer-safely from s0.  The deploy
 * counterpart of body_stmts_sim_ptr, which covers only runtime frames.
 * TOP-LEVEL: deploy_ctor_body_ptr (admitted until proved).
 *)
Theory ctorDeployMemoryRunPtrBody
Ancestors
  ctorDeployMemoryRunPtrDefs ctorDeployLoweringDefs gasSummary ptrSafeRun
  stmtSimDefs loweringPosts fragExec bodySim

Theorem deploy_ctor_body_ptr:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func
   mut am_c es0 s0 G0 tn0.
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
    stmt_state_rel dunit.cu_context func cenv
      (deploy_evaluation_context tops am tx)
      (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
    s0.vs_gas_readings = vs.vs_gas_readings /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    deploy_ptr_inv tops runtime_bc am tx imm G0 tn0 s0 /\
    (!body_cenv ee s G tn.
       same_frame cenv body_cenv /\
       stmt_state_rel dunit.cu_context func body_cenv
         (deploy_evaluation_context tops am tx) ee s /\
       ~s.vs_halted /\ s.vs_current_bb = st_exit.cs_current_bb /\
       s.vs_inst_idx = 0 /\
       deploy_ptr_inv tops runtime_bc am tx imm G tn s ==>
       ?fuel final.
         run_from fuel dunit.cu_context func s = Halt final /\
         ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel
           dunit.cu_context func [] G tn s) ==>
    (?s G tn cenv' ee.
       ~s.vs_halted /\ ~block_is_terminated sb /\
       s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts /\
       cenv_top_ext cenv cenv' ee.scopes /\
       stmt_state_rel dunit.cu_context func cenv'
         (deploy_evaluation_context tops am tx) ee s /\
       deploy_ptr_inv tops runtime_bc am tx imm G tn s /\
       !fuel r. run_from fuel dunit.cu_context func s = r /\
                (!e. r <> Error e) ==>
         ?fuel'. run_from fuel' dunit.cu_context func s0 = r /\
           (ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
              fuel dunit.cu_context func [] G tn s ==>
            ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
              fuel' dunit.cu_context func [] G0 tn0 s0)) \/
    (?fuel r. run_from fuel dunit.cu_context func s0 = r /\ exit_result r /\
              ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
                fuel dunit.cu_context func [] G0 tn0 s0)
Proof
  cheat
QED
