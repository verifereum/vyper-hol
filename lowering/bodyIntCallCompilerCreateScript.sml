Theory bodyIntCallCompilerCreate
Ancestors
  bodyIntCallCompilerRawSystem bodyIntCallCompilerContext
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit builtinCreate compileEnv

Theorem intcall_interval_check_create_result:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_check_create_result res rof a))
Proof
  strip_tac >> Cases_on `rof` >>
  simp[compile_check_create_result_def, comp_ignore_bind_def, intcall_interval_return] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_fresh_label, intcall_interval_emit_inst,
            intcall_interval_new_block, intcall_interval_emit_op,
            intcall_interval_alloc_buffer, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_create_dispatch:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_create_dispatch codep cl cv salt rof a))
Proof
  strip_tac >> Cases_on `salt` >> simp[compile_create_dispatch_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_op, intcall_interval_check_create_result]
QED

Theorem intcall_interval_create_proxy_buf:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_create_proxy_buf target a))
Proof
  strip_tac >> simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_void,
            intcall_interval_emit_op, intcall_interval_return])
QED

Theorem intcall_interval_create_copy:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_create_copy target cv salt rof a))
Proof
  strip_tac >> Cases_on `salt` >> Cases_on `rof` >>
  simp[compile_create_copy_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_alloc_dynamic, intcall_interval_return,
            intcall_interval_check_create_result])
QED

Theorem intcall_interval_create_blueprint_check:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_create_blueprint_check target off a))
Proof
  strip_tac >> simp[compile_create_blueprint_check_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_create_blueprint_append:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_create_blueprint_append target cv salt off sz ap al rof a))
Proof
  strip_tac >> Cases_on `salt` >> Cases_on `rof` >> Cases_on `al = Lit 0w` >>
  simp[compile_create_blueprint_append_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_alloc_dynamic, intcall_interval_copy_memory_dynamic,
            intcall_interval_return, intcall_interval_check_create_result])
QED
