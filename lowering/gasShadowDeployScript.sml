(* Deploy generator correspondence with identical layout parameters. *)
Theory gasShadowDeploy
Ancestors
  gasShadowModuleDefs gasShadowCompileStmt gasShadowCompileStmtBase
  gasShadowState gasShadow moduleLowering list compileEnv
  gasShadowModuleOps gasShadowModuleArgs gasShadowInternal
  gasShadowCompileContext gasShadowCompileStmtOps
  gasShadowCenv gasShadowCenvStmt gasShadowCenvModule

Theorem gas_shadow_compile_generate_deploy:
  !has_ctor runtime_size imm args data_size ints ce body pay nr key trans.
    gas_shadow_compiles
      (compile_generate_deploy has_ctor runtime_size imm args data_size
        ints ce body pay nr key trans)
      (compile_generate_deploy has_ctor runtime_size imm args data_size
        (MAP gas_shadow_internal_package ints)
        (gas_shadow_cenv ce) (MAP gas_shadow_stmt body) pay nr key trans)
Proof
  rpt gen_tac >> reverse (Cases_on `has_ctor`) >>
  simp[compile_generate_deploy_def, comp_ignore_bind_def]
  >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_simple_deploy,
          gas_shadow_compiles_return] >>
  rpt ((ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- (rpt IF_CASES_TAC >>
            simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
                 gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void,
                 gas_shadow_compiles_fixed_region_with_id,
                 gas_shadow_compiles_register_constructor_args,
                 gas_shadow_compiles_nonreentrant_lock,
                 gas_shadow_compiles_fresh_label, gas_shadow_compile_stmt]) >>
        gen_tac)
       ORELSE
       (ho_match_mp_tac gas_shadow_compiles_bind_cenv >> conj_tac
        >- simp[gas_shadow_compiles_register_constructor_args] >>
        conj_tac
        >- simp[gas_shadow_cenv_register_constructor_args] >>
        gen_tac)) >>
  ho_match_mp_tac gas_shadow_compiles_get_terminated >> gen_tac >>
  Cases_on `b` >> Cases_on `nr` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block,
       gas_shadow_compiles_nonreentrant_unlock,
       gas_shadow_compiles_constructor_epilogue,
       gas_shadow_compile_internal_fn_bodies]
QED
