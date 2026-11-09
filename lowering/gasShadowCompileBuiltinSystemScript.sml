Theory gasShadowCompileBuiltinSystem
Ancestors
  gasShadowCompileContext gasShadowCompileArith gasShadowState compileEnv builtinSystem

Theorem gas_shadow_compiles_msg_data_to_memory:
  gas_shadow_compiles compile_msg_data_to_memory compile_msg_data_to_memory
Proof
  simp[compile_msg_data_to_memory_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_dynamic, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_raw_call_outbuf:
  gas_shadow_compiles (compile_raw_call_outbuf max_outsize)
    (compile_raw_call_outbuf max_outsize)
Proof
  Cases_on `max_outsize > 0` >>
  simp[compile_raw_call_outbuf_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_return] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_raw_call_finish:
  gas_shadow_compiles
    (compile_raw_call_finish to_op data_ptr data_len gas_op value_op
      call_ty max_outsize revert_on_failure out_val out_ptr)
    (compile_raw_call_finish to_op data_ptr data_len gas_op value_op
      call_ty max_outsize revert_on_failure out_val out_ptr)
Proof
  Cases_on `call_ty` >> Cases_on `revert_on_failure` >>
  Cases_on `max_outsize > 0` >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_fresh_label, gas_shadow_compiles_new_block,
               gas_shadow_compiles_select, gas_shadow_compiles_return] >>
       gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_send:
  gas_shadow_compiles (compile_send to_op value_op gas_op)
    (compile_send to_op value_op gas_op)
Proof
  simp[compile_send_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_raw_revert:
  gas_shadow_compiles (compile_raw_revert data_ptr) (compile_raw_revert data_ptr)
Proof
  simp[compile_raw_revert_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_compiles_selfdestruct:
  gas_shadow_compiles (compile_selfdestruct to_op) (compile_selfdestruct to_op)
Proof
  simp[compile_selfdestruct_def, gas_shadow_compiles_emit_void]
QED
