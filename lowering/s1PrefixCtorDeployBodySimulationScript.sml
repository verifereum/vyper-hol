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
  rpt gen_tac >> strip_tac >>
  drule_all ctorDeployLoweringFrameTheory.deploy_ctor_body_frame >> strip_tac >>
  `~nr` by metis_tac[ctorDeployLoweringFrameTheory.deploy_ctor_not_nonreentrant] >>
  `cenv.ce_ctor_exit_label = SOME exit_lbl /\
   st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
   (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
      st_exit = ((), st_epilogue) /\
   compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
      st_epilogue = ((), st_final) /\ fn_has_code st_exit st_final func` by
    (qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
     simp[ctorDeployLoweringDefsTheory.deploy_ctor_code_def, compileEnvTheory.new_block_def] >>
     strip_tac >> gvs[]) >>
  `cenv.ce_modules = [(NONE,tops)]` by
    fs[bodySimTheory.body_inv_def, bodySimTheory.cenv_module_pins_def] >>
  `frame_ret_ok_full
     ((\H. deploy_dead H tops runtime_bc am tx), imm_len tops, NONE,
      dunit.cu_context, shadow_ctx, [], func, shadow_func)
     (deploy_evaluation_context tops am tx)
     (\H v ee gt r. constructor_return_q H func cenv
       (deploy_evaluation_context tops am tx) (LENGTH runtime_bc)
       (imm_len tops) nr nkey v ee r) cenv NoneT` by
    (irule ctorDeployMemoryRunPtrFrameRetTheory.constructor_frame_ret_ok_full >>
     simp[] >> metis_tac[]) >>
  `?args. lookup_function NONE tx.function_name Deploy tops =
     SOME (mut, nr, args, [], NoneT, source_body)` by
    fs[ctorDeployLoweringDefsTheory.deploy_ctor_start_def] >>
  pop_assum strip_assume_tac >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
     occurs_abi_decode_target target tops` by
    (`body = subst_consts_stmts (module_consts_env tops []) source_body` by
       metis_tac[ctorDeployLoweringEntrySelectionTheory.deploy_ctor_entry_selection_agrees] >>
     qpat_x_assum `body = _` SUBST_ALL_TAC >>
     `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
       (qpat_x_assum `deploy_source_ok _ _ _` mp_tac >>
        simp[ctorDeployDefsTheory.deploy_source_ok_def,
             e2eDeployDefsTheory.deploy_typing_ok_def] >> strip_tac >>
        drule vyperTypeContractModesTheory.check_contract_deploy_implies_runtime >>
        simp[]) >>
     pop_assum strip_assume_tac >>
     drule_all ctorDeployLoweringArmsTheory.deploy_ctor_constant_cells >> strip_tac >>
     `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
     rpt strip_tac >>
     drule_all constSubstStmtsPreserveTheory.checked_const_substitution_abi_decode_target >>
     metis_tac[bodyAbiDecodeTargetTheory.lookup_function_abi_decode_target_occurs]) >>
  `body_const_cells_agree [(NONE,tops)] (deploy_evaluation_context tops am tx)
     env_t (es0 with outcomes := SOME vs.vs_outcomes)` by
    simp[bodyFullPredsTheory.body_const_cells_agree_state_updates] >>
  qpat_x_assum `body_stmts_prefix_ok _ _`
    (mp_tac o REWRITE_RULE [body_stmts_prefix_ok_def]) >>
  disch_then drule_all >> disch_then (qspec_then `NoLoop` mp_tac) >>
  (* The prefix precondition is independent of the return postcondition. *)
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def]
QED
