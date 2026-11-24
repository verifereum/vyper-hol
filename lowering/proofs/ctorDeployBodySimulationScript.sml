(* The full body induction instantiated for a checked constructor. *)
Theory ctorDeployBodySimulation
Ancestors
  bodyFullShadowBodyInv
  ctorDeployLoweringFrame ctorDeployLoweringSourceOk
  ctorDeployMemoryRunPtrFrameRet ctorDeployLoweringDefs ctorReturnFrame
  bodySimFullMain bodyFullPreds bodySimFull bodyAbiDecodeTarget bodyLoopCalls
  e2eDeployDefs ctorDeployDefs compileEnv emitHelper
  vyperStorageLayoutSafety vyperLookupStorage vyperContext
  vyperInterpreter vyperState ctorDeployDeadLoad
  ctorDeployLoweringArms ctorDeployLoweringEntrySourceFrame ctorDeployLoweringEntryTransport
  constSubstStmts constSubstCorrect constSubst constSubstStmtsPreserve
  ctorDeployLoweringEntrySelection vyperTypeContractStaticMaps

val _ = Parse.hide "body";

Theorem deploy_ctor_body_substitution:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,F,body,am_c,es0) /\
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
  !os gx.
    eval_stmts (deploy_evaluation_context tops am tx)
      (subst_consts_stmts (module_consts_env tops []) body)
      (es0 with <|outcomes := os; gas_obs := gx|>) =
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <|outcomes := os; gas_obs := gx|>)
Proof
  strip_tac >>
  drule_all deploy_frame_source_start_setup >> strip_tac >>
  drule_all deploy_ctor_body_subst_context >> strip_tac >>
  rpt gen_tac >> irule const_subst_eval_stmts >>
  goal_assum (drule_at Any) >> qexists_tac `NoneT` >>
  fs[const_cells_agree_def]
QED

Theorem deploy_ctor_body_frag_full_base[local]:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func mut source_body am_c es0 shadow_ctx shadow_func.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    shadow_body_inv tops dunit.cu_context shadow_ctx /\
    deploy_ctor_start tops am tx (mut, nr, source_body, am_c, es0) ==>
    stmt_frag_full
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
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_body_frame >> strip_tac >>
  `~nr` by metis_tac[deploy_ctor_not_nonreentrant] >>
  `cenv.ce_ctor_exit_label = SOME exit_lbl /\
   st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
   (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
      st_exit = ((), st_epilogue) /\
   compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
      st_epilogue = ((), st_final) /\ fn_has_code st_exit st_final func` by
    (qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
     simp[deploy_ctor_code_def, new_block_def] >> strip_tac >> gvs[]) >>
  `frame_ret_ok_full
     ((\H. deploy_dead H tops runtime_bc am tx), imm_len tops, NONE,
      dunit.cu_context, shadow_ctx, [], func, shadow_func)
     (deploy_evaluation_context tops am tx)
     (\H v ee gt r. constructor_return_q H func cenv
       (deploy_evaluation_context tops am tx) (LENGTH runtime_bc)
       (imm_len tops) nr nkey v ee r) cenv NoneT` by
    (irule constructor_frame_ret_ok_full >> simp[] >> metis_tac[]) >>
  `?args. lookup_function NONE tx.function_name Deploy tops =
     SOME (mut, nr, args, [], NoneT, source_body)` by
    (qpat_assum `deploy_ctor_start _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [deploy_ctor_start_def]) >>
     metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `struct_args_unique tops` by
    metis_tac[deploy_source_ok_struct_args_unique] >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
     occurs_abi_decode_target target tops` by
    (`body = subst_consts_stmts (module_consts_env tops []) source_body` by
       metis_tac[deploy_ctor_entry_selection_agrees] >>
     qpat_x_assum `body = _` SUBST_ALL_TAC >>
     `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
       fs[deploy_source_ok_def, deploy_typing_ok_constants_ready] >>
     pop_assum strip_assume_tac >>
     drule_all deploy_ctor_constant_cells >> strip_tac >>
     `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
     rpt strip_tac >>
     drule_all checked_const_substitution_abi_decode_target >>
     metis_tac[lookup_function_abi_decode_target_occurs]) >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[deploy_source_ok_def, deploy_typing_ok_constants_ready] >>
  pop_assum strip_assume_tac >>
  drule bodyLoopCallsTheory.checked_module_loop_calls_ok >> disch_then assume_tac >>
  `stmts_loop_calls_ok [(NONE,tops)] body` by
    (`body = subst_consts_stmts (module_consts_env tops []) source_body` by
       metis_tac[deploy_ctor_entry_selection_agrees] >>
     qpat_assum `body = subst_consts_stmts _ source_body` SUBST1_TAC >>
     `stmts_loop_calls_ok [(NONE,tops)] source_body` by
       (drule_all_then ACCEPT_TAC bodyLoopCallsTheory.checked_deploy_body_loop_calls_ok) >>
     drule_all deploy_ctor_constant_cells >> strip_tac >>
     drule_all_then ACCEPT_TAC bodyLoopCallsTheory.checked_subst_consts_loop_calls_ok) >>
  qspecl_then [`\H. deploy_dead H tops runtime_bc am tx`, `imm_len tops`,
    `NONE`, `[]`, `tops`, `bindings`, `dunit.cu_context`, `shadow_ctx`,
    `func`, `shadow_func`, `cenv`, `deploy_evaluation_context tops am tx`,
    `env_t`, `env'`, `NoneT`, `NoLoop`,
    `\H v ee gt r. constructor_return_q H func cenv
       (deploy_evaluation_context tops am tx) (LENGTH runtime_bc)
       (imm_len tops) nr nkey v ee r`, `body`,
    `es0 with outcomes := SOME vs.vs_outcomes`]
    mp_tac body_stmts_sim_full >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem deploy_ctor_body_internal_constant_defaults:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func mut source_body am_c es0 shadow_ctx shadow_func.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    internal_defaults_const_names tops /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    gas_variant vs (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    shadow_body_inv tops dunit.cu_context shadow_ctx /\
    deploy_ctor_start tops am tx (mut, nr, source_body, am_c, es0) ==>
    stmt_frag_full
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
  metis_tac[deploy_ctor_body_frag_full_base]
QED

Theorem deploy_ctor_body_frag_full:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func mut source_body am_c es0 shadow_ctx shadow_func.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    gas_variant vs (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    shadow_body_inv tops dunit.cu_context shadow_ctx /\
    deploy_ctor_start tops am tx (mut, nr, source_body, am_c, es0) ==>
    stmt_frag_full
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
  metis_tac[deploy_ctor_body_frag_full_base]
QED
