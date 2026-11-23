(* Shadow correspondence for positional registration, which returns an env. *)
Theory gasShadowRuntimeRegisterEnv
Ancestors
  gasShadowModuleArgs gasShadowCompileStmtBase gasShadowCompileContext
  gasShadowCompileBase moduleLowering compileEnv

Theorem compile_decode_args_gas_shadow_env[simp]:
  !args ce off opc hi base.
    compile_decode_args (gas_shadow_env sd ce) args off opc hi base =
    compile_decode_args ce args off opc hi base
Proof
  Induct >> rpt gen_tac
  >- simp[compile_decode_args_def] >>
  PairCases_on `h` >> simp[compile_decode_args_def]
QED

Theorem gas_shadow_compiles_env_register_positional_args:
  !args ce off.
    gas_shadow_compiles_env sd (compile_register_positional_args ce args off)
      (compile_register_positional_args (gas_shadow_env sd ce) args off)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_register_positional_args_def, gas_shadow_compiles_env_return] >>
  PairCases_on `h` >> simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `var_location_memory_size loc` >> simp[] >>
  ho_match_mp_tac gas_shadow_compiles_bind_env >> conj_tac
  >- simp[gas_shadow_compiles_alloc_buffer] >>
  gen_tac >> ho_match_mp_tac gas_shadow_compiles_env_bind_env >> conj_tac
  >- (irule gas_shadow_compiles_env_return >>
      rw[gas_shadow_env_def, compile_env_component_equality]) >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind_env,
       gas_shadow_compiles_decode_args]
QED
