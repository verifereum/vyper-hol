(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringFallthrough
Ancestors
  ctorDeployLoweringDefs ctorReturnFrame stmtSimDefs

(* A body that falls off its end at sb runs the jump to the exit block, the
   unlock and the epilogue (constructor_exit_run). *)
Theorem deploy_ctor_fallthrough:
  !tops rpolicy runtime_bc dunit
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func cx cenv' ee t.
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
    ?fuel final.
      run_from fuel dunit.cu_context func t = Halt final /\
      constructor_return_q func cenv cx (LENGTH runtime_bc) (imm_len tops)
        nr nkey NoneV (ee with scopes := []) (Halt final)
Proof
  cheat
QED
