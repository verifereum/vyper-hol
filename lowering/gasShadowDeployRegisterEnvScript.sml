(* Constructor argument registration changes only the variables of the env. *)
Theory gasShadowDeployRegisterEnv
Ancestors
  gasShadowCompileBase moduleLowering compileEnv pair

Theorem compile_register_constructor_args_gas_shadow_env:
  !args ce off size s.
    compile_register_constructor_args (gas_shadow_env sd ce) args off size s =
    (gas_shadow_env sd ## I) (compile_register_constructor_args ce args off size s)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_register_constructor_args_def, comp_return_def] >>
  PairCases_on `h` >> simp[compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `var_location_memory_size loc` >> simp[] >>
  rename1 `SOME mem_size` >>
  Cases_on `compile_alloc_buffer mem_size s` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `∀f. (gas_shadow_env sd ce with ce_vars updated_by f) =
        gas_shadow_env sd (ce with ce_vars updated_by f)` by
    rw[gas_shadow_env_def, compile_env_component_equality] >>
  simp[compile_decode_args_def] >> pairarg_tac >> simp[]
QED
