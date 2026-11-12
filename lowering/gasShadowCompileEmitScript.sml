Theory gasShadowCompileEmit
Ancestors
  gasShadowState compileEnv emitHelper

Theorem gas_shadow_compiles_fresh_vars:
  !n. gas_shadow_compiles (fresh_vars n) (fresh_vars n)
Proof
  Induct >> simp[fresh_vars_def, gas_shadow_compiles_return] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_fresh_var] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_emit_multi_op:
  gas_shadow_compiles (emit_multi_op opc ops n) (emit_multi_op opc ops n)
Proof
  simp[emit_multi_op_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_fresh_vars, gas_shadow_compiles_emit_inst] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED
