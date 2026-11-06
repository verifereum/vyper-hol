(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringFrame
Ancestors
  ctorDeployLoweringDefs ctorDeployImmBudget o1PassContract bodySim e2eDefs callTrace

(* body_stmts_sim's premises for the constructor body at its start, and the
   side conditions of constructor_frame_ret_ok and constructor_exit_run. *)
Theorem deploy_ctor_body_frame:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut am_c es0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    call_outcomes_ok am tx (MAP SND (call_trace es)) /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) ==>
    body_inv tops dunit.cu_context cenv (deploy_evaluation_context tops am tx) /\
    cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe (deploy_evaluation_context tops am tx) /\
            (deploy_evaluation_context tops am tx).nonreentrant_slot = SOME nkey) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       !x. imm = Var x ==> not_fresh_at st_epilogue x) /\
    ?bindings env_t env'.
      supported_stmts tops bindings body /\
      expr_sim_inv cenv (deploy_evaluation_context tops am tx) env_t
        (es0 with outcomes := SOME vs.vs_outcomes) /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t NoneT body = SOME env' /\
      EVERY (stmt_exprs_ok cenv) body /\
      call_evaluation_safe (deploy_evaluation_context tops am tx) (int_calls_stmts body)
Proof
  cheat
QED
