(* Internal function and package-list shadow correspondence. *)
Theory gasShadowInternal
Ancestors
  gasShadowModuleOps gasShadowModuleDefs gasShadowCompileStmt
  gasShadowCenv gasShadowCenvStmt gasShadowCenvModule
  gasShadowCompileStmtBase gasShadowCompileStmtOps gasShadowCompileContext
  gasShadowState moduleLowering compileEnv

Theorem gas_shadow_compile_internal_function:
  !ce ps rb nr key trans view ctor imm body ret.
    gas_shadow_compiles
      (compile_internal_function ce ps rb nr key trans view ctor imm body ret)
      (compile_internal_function (gas_shadow_cenv ce) ps rb nr key trans view
        ctor imm (MAP gas_shadow_stmt body) ret)
Proof
  rpt gen_tac >>
  simp[compile_internal_function_def, comp_ignore_bind_def] >>
  rpt ((ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- (rpt IF_CASES_TAC >>
            simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
                 gas_shadow_compiles_emit_op,
                 gas_shadow_compiles_internal_param_decls,
                 gas_shadow_compiles_fixed_region_with_id,
                 gas_shadow_compiles_materialize_internal_params]) >> gen_tac)
       ORELSE
       (ho_match_mp_tac gas_shadow_compiles_bind_cenv >> conj_tac
        >- simp[gas_shadow_compiles_return,
                gas_shadow_compiles_materialize_internal_params] >>
        conj_tac
        >- simp[comp_return_def, gas_shadow_cenv_materialize_internal_params] >>
        gen_tac)) >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `ret` >> simp[gas_shadow_compiles_return] >>
      IF_CASES_TAC >>
      simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
           gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return]) >>
  gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `nr` >> simp[gas_shadow_compiles_nonreentrant_lock,
                           gas_shadow_compiles_return]) >>
  gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compile_stmt] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_get_terminated >> gen_tac >>
  Cases_on `b` >> Cases_on `nr` >> Cases_on `ret` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_nonreentrant_unlock, gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_compile_internal_fn_bodies:
  !ints. gas_shadow_compiles (compile_internal_fn_bodies ints)
    (compile_internal_fn_bodies (MAP gas_shadow_internal_package ints))
Proof
  Induct >> simp[compile_internal_fn_bodies_def, gas_shadow_compiles_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[gas_shadow_internal_package_def, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_new_block, gas_shadow_compile_internal_function]
QED
