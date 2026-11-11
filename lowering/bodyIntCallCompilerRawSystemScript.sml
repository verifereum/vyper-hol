Theory bodyIntCallCompilerRawSystem
Ancestors
  bodyIntCallCompilerScalar bodyIntCallCompilerContext
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit builtinSystem context compileEnv

Theorem intcall_interval_alloc_dynamic:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_alloc_dynamic sz a))
Proof
  simp[compile_alloc_dynamic_def, intcall_interval_emit_op]
QED

Theorem intcall_interval_msg_data_to_memory:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_msg_data_to_memory a))
Proof
  strip_tac >> simp[compile_msg_data_to_memory_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_alloc_dynamic,
            intcall_interval_emit_void, intcall_interval_return])
QED

Theorem intcall_interval_raw_call_outbuf:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_raw_call_outbuf n a))
Proof
  strip_tac >> simp[compile_raw_call_outbuf_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_return])
QED

Theorem intcall_interval_raw_revert:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_raw_revert dp a))
Proof
  strip_tac >> simp[compile_raw_revert_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_inst])
QED

Theorem intcall_interval_raw_call_finish:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_raw_call_finish dest dp dl gas value ct n rof ov op a))
Proof
  strip_tac >> Cases_on `ct` >> Cases_on `rof` >>
  Cases_on `n > 0` >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_inst,
            intcall_interval_emit_void, intcall_interval_fresh_label,
            intcall_interval_new_block, intcall_interval_alloc_buffer,
            intcall_interval_select, intcall_interval_return])
QED
