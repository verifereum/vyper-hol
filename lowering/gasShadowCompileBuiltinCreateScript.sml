Theory gasShadowCompileBuiltinCreate
Ancestors
  gasShadowCompileContext gasShadowState compileEnv builtinCreate

Theorem gas_shadow_compiles_check_create_result:
  gas_shadow_compiles (compile_check_create_result result revert_on_failure)
    (compile_check_create_result result revert_on_failure)
Proof
  Cases_on `revert_on_failure` >>
  simp[compile_check_create_result_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_fresh_label, gas_shadow_compiles_new_block] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_create_dispatch:
  gas_shadow_compiles
    (compile_create_dispatch code_ptr code_len value_op salt_opt revert_on_failure)
    (compile_create_dispatch code_ptr code_len value_op salt_opt revert_on_failure)
Proof
  Cases_on `salt_opt` >> simp[compile_create_dispatch_def] >>
  match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_check_create_result]
QED

Theorem gas_shadow_compiles_create_proxy_buf:
  gas_shadow_compiles (compile_create_proxy_buf target_op)
    (compile_create_proxy_buf target_op)
Proof
  simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_return] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_create_copy:
  gas_shadow_compiles
    (compile_create_copy target_op value_op salt_opt revert_on_failure)
    (compile_create_copy target_op value_op salt_opt revert_on_failure)
Proof
  Cases_on `salt_opt` >> Cases_on `revert_on_failure` >>
  simp[compile_create_copy_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_dynamic, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_return] >>
       gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_check_create_result]
QED

Theorem gas_shadow_compiles_create_blueprint_check:
  gas_shadow_compiles (compile_create_blueprint_check target_op code_offset_op)
    (compile_create_blueprint_check target_op code_offset_op)
Proof
  simp[compile_create_blueprint_check_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_create_blueprint_append:
  gas_shadow_compiles
    (compile_create_blueprint_append target_op value_op salt_opt code_offset_op
      code_size args_ptr args_len revert_on_failure)
    (compile_create_blueprint_append target_op value_op salt_opt code_offset_op
      code_size args_ptr args_len revert_on_failure)
Proof
  Cases_on `salt_opt` >> Cases_on `revert_on_failure` >>
  Cases_on `args_len = Lit 0w` >>
  simp[compile_create_blueprint_append_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_dynamic, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_return,
               gas_shadow_compiles_copy_memory_dynamic,
               gas_shadow_compiles_bind] >>
       gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_check_create_result]
QED
