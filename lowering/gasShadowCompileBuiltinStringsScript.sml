Theory gasShadowCompileBuiltinStrings
Ancestors
  gasShadowCompileContext gasShadowState compileEnv builtinStrings

Theorem gas_shadow_compiles_uint2str:
  gas_shadow_compiles (compile_uint2str val_op n_digits buf_size)
    (compile_uint2str val_op n_digits buf_size)
Proof
  simp[compile_uint2str_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_fresh_var,
               gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED
