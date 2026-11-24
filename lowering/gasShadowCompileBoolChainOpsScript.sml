Theory gasShadowCompileBoolChainOps
Ancestors
  gasShadow gasShadowState exprLowering compileEnv list

Theorem gas_shadow_compiles_bool_chain_ops:
  (!e. gas_shadow_compiles (lower_value f ce (BaseT BoolT) e)
         (lower_value g ce' (BaseT BoolT)
           (if m then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_bool_chain_ops f ce d r l es)
    (compile_bool_chain_ops g ce' d r l
      (if m then MAP gas_shadow_expr es else es))
Proof
  Induct_on `es`
  >- simp[compile_bool_chain_ops_def, gas_shadow_compiles_return] >>
  rpt strip_tac >> Cases_on `es` >> Cases_on `m` >> Cases_on `d` >>
  gvs[compile_bool_chain_ops_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
               gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block] >>
       gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_emit_inst]
QED
