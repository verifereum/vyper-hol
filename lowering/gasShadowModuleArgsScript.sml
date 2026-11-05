(* Constructor argument operations on arbitrary descriptors. *)
Theory gasShadowModuleArgs
Ancestors
  gasShadowModuleOps gasShadowCompileAbi gasShadowCompileContext gasShadowState
  moduleLowering compileEnv

Theorem gas_shadow_compiles_decode_args:
  !args ce off opc hi base.
    gas_shadow_compiles (compile_decode_args ce args off opc hi base)
      (compile_decode_args ce args off opc hi base)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_decode_args_def, gas_shadow_compiles_return] >>
  PairCases_on `h` >>
  Cases_on `h1` >> Cases_on `h2` >>
  simp[compile_decode_args_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op,
               gas_shadow_compiles_abi_clamp_basetype] >> gen_tac) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return] >>
  rename1 `SOME loc` >>
  Cases_on `var_location_decode_operand loc` >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_return, gas_shadow_compiles_emit_op,
       gas_shadow_compiles_emit_void, gas_shadow_compiles_abi_decode_to_buf]
QED

Theorem gas_shadow_compiles_register_constructor_args:
  !args ce off size.
    gas_shadow_compiles (compile_register_constructor_args ce args off size)
      (compile_register_constructor_args ce args off size)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_register_constructor_args_def, gas_shadow_compiles_return] >>
  PairCases_on `h` >> simp[compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return] >>
  rename1 `SOME loc` >> Cases_on `var_location_memory_size loc` >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_return, gas_shadow_compiles_alloc_buffer,
       gas_shadow_compiles_decode_args]
QED
