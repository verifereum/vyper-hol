(* Keyword registration updates variables, not function defaults. *)
Theory gasShadowRuntimeKwargEnv
Ancestors
  gasShadowCompileBase moduleLowering compileEnv

Theorem compile_register_kwarg_vars_gas_shadow_env:
  !kwvars ce.
    compile_register_kwarg_vars (gas_shadow_env sd ce) kwvars =
    gas_shadow_env sd (compile_register_kwarg_vars ce kwvars)
Proof
  Induct
  >- simp[compile_register_kwarg_vars_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[compile_register_kwarg_vars_def] >>
  `gas_shadow_env sd
     (ce with ce_vars := ce.ce_vars |+ (h0,PtrVar h1 (type_memory_bytes ce h2))) =
   gas_shadow_env sd ce with ce_vars :=
     ce.ce_vars |+ (h0,PtrVar h1 (type_memory_bytes ce h2))` by
    rw[gas_shadow_env_def, compile_env_component_equality] >>
  pop_assum (SUBST1_TAC o SYM) >> simp[]
QED
