(* The full body induction instantiated for a checked constructor. *)
Theory ctorDeployBodySimulation
Ancestors
  ctorDeployLoweringFrame ctorDeployLoweringSourceOk
  ctorDeployMemoryRunPtrFrameRet ctorDeployLoweringDefs ctorReturnFrame
  bodySimFullMain bodyFullPreds bodySimFull bodyAbiDecodeTarget
  e2eDeployDefs ctorDeployDefs compileEnv emitHelper
  vyperStorageLayoutSafety vyperLookupStorage vyperContext
  vyperInterpreter vyperState

val _ = Parse.hide "body";

Theorem deploy_ctor_body_frag_full:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func mut am_c es0 shadow_ctx shadow_func.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) ==>
    stmt_frag_full
      ((\H. deploy_dead H tops runtime_bc am tx), imm_len tops, NONE,
       dunit.cu_context, shadow_ctx, [], func, shadow_func)
      (deploy_evaluation_context tops am tx) NoLoop
      (\H v ee gt r. constructor_return_q H func cenv
        (deploy_evaluation_context tops am tx) (LENGTH runtime_bc)
        (imm_len tops) nr nkey v ee r)
      cenv (stmts_env cenv NoLoop NoneT body)
      (stmts_env cenv NoLoop NoneT (MAP gas_shadow_stmt body))
      (eval_stmts (deploy_evaluation_context tops am tx) body)
      (es0 with outcomes := SOME vs.vs_outcomes)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\outcome.
     contract_storage_well_formed
       (initial_evaluation_context am.sources am.layouts tx NONE)
       (initial_state (am with <|accounts := outcome.co_accounts;
                                tStorage := outcome.co_tStorage|>) []))
     (MAP SND (call_trace es))` by
    (`ALOOKUP am.sources tx.target = NONE` by fs[deploy_state_rel_def] >>
     simp[listTheory.EVERY_MEM, contract_storage_well_formed_def,
          well_formed_storage_def, storage_var_in_range_def,
          storage_var_info_def, declared_storage_region_def,
          get_module_code_def, initial_evaluation_context_def]) >>
  `call_outcomes_ok am tx (MAP SND (call_trace es))` by
    metis_tac[deploy_state_rel_call_outcomes_ok] >>
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
     SOME (mut, nr, args, [], NoneT, body)` by
    (qpat_assum `deploy_ctor_start _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [deploy_ctor_start_def]) >>
     metis_tac[]) >>
  qspecl_then [`\H. deploy_dead H tops runtime_bc am tx`, `imm_len tops`,
    `NONE`, `[]`, `tops`, `bindings`, `dunit.cu_context`, `shadow_ctx`,
    `func`, `shadow_func`, `cenv`, `deploy_evaluation_context tops am tx`,
    `env_t`, `env'`, `NoneT`, `NoLoop`,
    `\H v ee gt r. constructor_return_q H func cenv
       (deploy_evaluation_context tops am tx) (LENGTH runtime_bc)
       (imm_len tops) nr nkey v ee r`, `body`,
    `es0 with outcomes := SOME vs.vs_outcomes`]
    mp_tac body_stmts_sim_full >>
  impl_tac >- (simp[] >> metis_tac[lookup_function_abi_decode_target_occurs]) >>
  simp[]
QED
