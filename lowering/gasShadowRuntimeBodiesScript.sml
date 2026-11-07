(* Function-stmts consumers of statement-list correspondence. *)
Theory gasShadowRuntimeBodies
Ancestors
  gasShadowModuleOps gasShadowInternal gasShadowRuntimeOps gasShadowModuleDefs gasShadowCompileStmt
  gasShadowCenv gasShadowCenvStmt gasShadowCenvModule
  gasShadowCompileStmtBase gasShadowCompileStmtOps gasShadowCompileContext
  gasShadowState gasShadow moduleLowering compileEnv emitHelper stmtLowering list

Theorem gas_shadow_compiles_compile_guarded_body:
  gas_shadow_compiles (compile_guarded_body ce nr key trans view stmts ret)
    (compile_guarded_body (gas_shadow_cenv ce) nr key trans view
       (MAP gas_shadow_stmt stmts) ret)
Proof
  rewrite_tac[compile_guarded_body_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `nr` >> simp[gas_shadow_compiles_nonreentrant_lock,
                            gas_shadow_compiles_return]) >>
  gen_tac >> BETA_TAC >> match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[CONJUNCT2 gas_shadow_compile_stmt] >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac gas_shadow_compiles_get_terminated >> gen_tac >>
  Cases_on `b` >> Cases_on `nr` >> Cases_on `ret` >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_bind,
       gas_shadow_compiles_nonreentrant_unlock, gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_compiles_compile_external_function_body:
  gas_shadow_compiles
    (compile_external_function_body ce args nr key trans view stmts ret)
    (compile_external_function_body (gas_shadow_cenv ce) args nr key trans view
      (MAP gas_shadow_stmt stmts) ret)
Proof
  simp[compile_external_function_body_def] >>
  ho_match_mp_tac gas_shadow_compiles_bind_cenv >>
  simp[gas_shadow_cenv_register_positional_args,
       gas_shadow_compiles_compile_register_positional_args,
       gas_shadow_compiles_compile_guarded_body]
QED

Theorem gas_shadow_compiles_compile_fallback_body:
  gas_shadow_compiles (compile_fallback_body ce pay nr key trans view stmts ret)
    (compile_fallback_body (gas_shadow_cenv ce) pay nr key trans view
       (MAP gas_shadow_stmt stmts) ret)
Proof
  Cases_on `pay` >>
  simp[compile_fallback_body_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_op_same, gas_shadow_compiles_emit_void,
       gas_shadow_compiles_compile_guarded_body]
QED

Theorem gas_shadow_compiles_compile_external_fn_bodies:
  !exts. gas_shadow_compiles (compile_external_fn_bodies exts)
    (compile_external_fn_bodies (MAP gas_shadow_external_package exts))
Proof
  Induct >> simp[compile_external_fn_bodies_def, gas_shadow_compiles_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def, gas_shadow_external_package_def,
       comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_new_block, gas_shadow_compiles_compile_entry_checks,
       gas_shadow_compiles_compile_external_function_body]
QED

