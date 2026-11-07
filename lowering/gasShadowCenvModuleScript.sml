(* The module lowering under the gas-shadow compile env: argument decoding
   ignores the internal functions' default arguments, and the steps that
   extend the env return the shadowed env of their own. *)
Theory gasShadowCenvModule
Ancestors
  gasShadowCenv gasShadowState moduleLowering compileEnv list pair

Theorem gas_shadow_cenv_decode_args[simp]:
  !xs c off opc hi base.
    compile_decode_args (gas_shadow_cenv c) xs off opc hi base =
    compile_decode_args c xs off opc hi base
Proof
  Induct >> simp[compile_decode_args_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[compile_decode_args_def]
QED

Theorem gas_shadow_cenv_register_positional_args:
  !xs c off s.
    compile_register_positional_args (gas_shadow_cenv c) xs off s =
    (gas_shadow_cenv (FST (compile_register_positional_args c xs off s)),
     SND (compile_register_positional_args c xs off s))
Proof
  Induct >> simp[compile_register_positional_args_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_register_positional_args_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem gas_shadow_cenv_register_constructor_args:
  !xs c off size s.
    compile_register_constructor_args (gas_shadow_cenv c) xs off size s =
    (gas_shadow_cenv (FST (compile_register_constructor_args c xs off size s)),
     SND (compile_register_constructor_args c xs off size s))
Proof
  Induct >> simp[compile_register_constructor_args_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_register_constructor_args_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem gas_shadow_cenv_materialize_internal_params:
  !ps c s.
    materialize_internal_params (gas_shadow_cenv c) ps s =
    (gas_shadow_cenv (FST (materialize_internal_params c ps s)),
     SND (materialize_internal_params c ps s))
Proof
  Induct >> simp[materialize_internal_params_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[materialize_internal_params_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED
