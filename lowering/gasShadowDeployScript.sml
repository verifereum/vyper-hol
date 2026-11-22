(* Deploy generator correspondence with identical layout parameters. *)
Theory gasShadowDeploy
Ancestors
  gasShadowModuleDefs gasShadowCompileStmt gasShadowCompileStmtBase
  gasShadowState gasShadow moduleLowering list compileEnv
  gasShadowModuleOps gasShadowModuleArgs gasShadowInternal
  gasShadowCompileContext gasShadowCompileStmtOps gasShadowDeployRegisterEnv

Theorem gas_shadow_compile_generate_deploy:
  !has_ctor runtime_size imm args data_size ints ce body pay nr key trans.
    gas_shadow_compiles
      (compile_generate_deploy has_ctor runtime_size imm args data_size
        ints ce body pay nr key trans)
      (compile_generate_deploy has_ctor runtime_size imm args data_size
        (MAP gas_shadow_internal_package ints)
        (gas_shadow_env sd ce) (MAP gas_shadow_stmt body) pay nr key trans)
Proof
  rpt gen_tac >>
  qabbrev_tac `nrinfo = ce.ce_nonreentrant` >> PairCases_on `nrinfo` >>
  reverse (Cases_on `has_ctor`) >>
  simp[compile_generate_deploy_def, comp_ignore_bind_def]
  >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_simple_deploy,
          gas_shadow_compiles_return] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `pay` >>
      simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
           gas_shadow_compiles_return, gas_shadow_compiles_emit_op,
           gas_shadow_compiles_emit_void]) >>
  gen_tac >> ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `0 < imm` >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
           gas_shadow_compiles_fixed_region_with_id]) >>
  gen_tac >> irule gas_shadow_compiles_env_bind >> qexists `sd` >> reverse conj_tac
  >- (`!opt. (gas_shadow_env sd ce with ce_imm_alloca := opt) =
               gas_shadow_env sd (ce with ce_imm_alloca := opt)` by
         rw[gasShadowCompileBaseTheory.gas_shadow_env_def,
            compile_env_component_equality] >>
       simp[gas_shadow_compiles_env_def,
            compile_register_constructor_args_gas_shadow_env] >>
       mp_tac gas_shadow_compiles_register_constructor_args >>
       simp[gas_shadow_compiles_def] >> metis_tac[]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `nr` >>
      simp[gas_shadow_compiles_nonreentrant_lock, gas_shadow_compiles_return]) >>
  gen_tac >> ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_fresh_label] >>
  gen_tac >> ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (`!env lbl. (gas_shadow_env sd env with ce_ctor_exit_label := lbl) =
                gas_shadow_env sd (env with ce_ctor_exit_label := lbl)` by
        rw[gasShadowCompileBaseTheory.gas_shadow_env_def,
           compile_env_component_equality] >>
      simp[gas_shadow_compile_stmt_env]) >>
  gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_get_terminated >> qx_gen_tac `b` >>
  Cases_on `b` >> Cases_on `nr` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block,
       gas_shadow_compiles_nonreentrant_unlock,
       gas_shadow_compiles_constructor_epilogue,
       gas_shadow_compile_internal_fn_bodies]
QED
