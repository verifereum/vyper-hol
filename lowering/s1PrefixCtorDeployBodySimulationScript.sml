(* Request-prefix companion to ctorDeployBodySimulation. *)
Theory s1PrefixCtorDeployBodySimulation
Ancestors
  s1PrefixPreds ctorDeployBodySimulation s1PrefixDefs

val _ = Parse.hide "body";

Theorem deploy_ctor_body_frag_prefix:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func mut source_body am_c es0 shadow_ctx shadow_func.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    ~internal_defaults_msg_gas tops /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    gas_variant vs (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    shadow_body_inv tops dunit.cu_context shadow_ctx /\
    deploy_ctor_start tops am tx (mut, nr, source_body, am_c, es0) /\
    body_stmts_prefix_ok (deploy_evaluation_context tops am tx) body ==>
    stmt_frag_prefix
      ((\H. deploy_dead H tops runtime_bc am tx), imm_len tops, NONE,
       dunit.cu_context, shadow_ctx, [], func, shadow_func)
      (deploy_evaluation_context tops am tx) NoLoop
      (\H v ee gt r. constructor_return_q H func cenv
        (deploy_evaluation_context tops am tx) (LENGTH runtime_bc)
        (imm_len tops) nr nkey v ee r)
      cenv (stmts_env cenv NoLoop NoneT body)
      (stmts_env (gas_shadow_env T cenv) NoLoop NoneT (MAP gas_shadow_stmt body))
      (eval_stmts (deploy_evaluation_context tops am tx) body)
      (es0 with outcomes := SOME vs.vs_outcomes)
Proof
  cheat
QED
