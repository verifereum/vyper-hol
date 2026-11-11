Theory bodyIntCallCompilerRead
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  exprLowering builtinSimple builtinMisc compileEnv

Theorem intcall_interval_env_var:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_env_var ev a))
Proof
  strip_tac >> Cases_on `ev` >>
  simp[compile_env_var_def, intcall_interval_emit_op] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op])
QED

Theorem intcall_interval_bytestring_hash:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_bytestring_hash p a))
Proof
  strip_tac >> simp[compile_bytestring_hash_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op])
QED

Theorem intcall_interval_builtin_len:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_builtin_len ctor imm p loc a))
Proof
  simp[compile_builtin_len_def, intcall_interval_ptr_load]
QED

Theorem intcall_interval_builtin_calldatasize:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_builtin_calldatasize a))
Proof
  simp[compile_builtin_calldatasize_def, intcall_interval_emit_op]
QED

Theorem intcall_interval_blockhash:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_blockhash n a))
Proof
  strip_tac >> simp[compile_blockhash_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_blobhash:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_blobhash n a))
Proof
  simp[compile_blobhash_def, intcall_interval_emit_op]
QED

Theorem intcall_interval_ecrecover:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_ecrecover h v r s a))
Proof
  strip_tac >> simp[compile_ecrecover_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_void, intcall_interval_emit_op])
QED

Theorem intcall_interval_ecadd_points:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_ecadd_points p q a))
Proof
  strip_tac >> simp[compile_ecadd_points_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_void, intcall_interval_emit_op])
QED

Theorem intcall_interval_ecmul_point:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_ecmul_point p s a))
Proof
  strip_tac >> simp[compile_ecmul_point_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_void, intcall_interval_emit_op])
QED
