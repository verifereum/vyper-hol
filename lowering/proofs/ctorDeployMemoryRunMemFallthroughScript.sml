(* A constructor body that falls off its end at sb runs the jump to the exit
 * block, the unlock and the epilogue memory-safely, to a halt.  The memory
 * twin of deploy_ctor_fallthrough.
 * TOP-LEVEL: deploy_ctor_fallthrough_mem_safe (admitted until proved).
 *)
Theory ctorDeployMemoryRunMemFallthrough
Ancestors
  ctorDeployLoweringDefs stmtSimDefs memSafeRun

Theorem deploy_ctor_fallthrough_mem_safe:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func cx cenv' ee t.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    cenv.ce_is_ctor /\ cenv_top_ext cenv cenv' ee.scopes /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       !x. imm = Var x ==> not_fresh_at st_epilogue x) /\
    stmt_state_rel dunit.cu_context func cenv' cx ee t /\ ~t.vs_halted /\
    ~block_is_terminated sb /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?fuel. mem_safe_run fuel dunit.cu_context func t /\
           !e. run_from fuel dunit.cu_context func t <> Error e
Proof
  cheat
QED
