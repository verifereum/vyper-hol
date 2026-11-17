(* Equal-input module operations preserve shadow compilation. *)
Theory gasShadowModuleOps
Ancestors
  gasShadowCompileStmtOps gasShadowCompileContext gasShadowState moduleLowering
  compileEnv context

Theorem gas_shadow_compiles_internal_param_decls:
  !ps idx. gas_shadow_compiles (compile_internal_param_decls ps idx)
    (compile_internal_param_decls ps idx)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_internal_param_decls_def, gas_shadow_compiles_return] >>
  PairCases_on `h` >>
  simp[compile_internal_param_decls_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_op, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_materialize_internal_params:
  !ps ce. gas_shadow_compiles (materialize_internal_params ce ps)
    (materialize_internal_params ce ps)
Proof
  Induct >> rpt gen_tac
  >- simp[materialize_internal_params_def, gas_shadow_compiles_return] >>
  PairCases_on `h` >>
  simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[gas_shadow_compiles_bind, comp_ignore_bind_def,
       gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_nonreentrant_lock:
  !key trans view. gas_shadow_compiles (compile_nonreentrant_lock key trans view)
    (compile_nonreentrant_lock key trans view)
Proof
  rpt gen_tac >> Cases_on `trans` >> Cases_on `view` >>
  simp[compile_nonreentrant_lock_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_constructor_epilogue:
  !size imm buf. gas_shadow_compiles (compile_constructor_epilogue size imm buf)
    (compile_constructor_epilogue size imm buf)
Proof
  rpt gen_tac >> simp[compile_constructor_epilogue_def] >> IF_CASES_TAC >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_return, gas_shadow_compiles_emit_op,
       gas_shadow_compiles_emit_void, gas_shadow_compiles_emit_inst,
       gas_shadow_compiles_alloc_buffer]
QED

Theorem gas_shadow_compiles_simple_deploy:
  !size imm. gas_shadow_compiles (compile_simple_deploy size imm)
    (compile_simple_deploy size imm)
Proof
  simp[compile_simple_deploy_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_void, gas_shadow_compiles_emit_inst,
       gas_shadow_compiles_alloc_buffer]
QED
