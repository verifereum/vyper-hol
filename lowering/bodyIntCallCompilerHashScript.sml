Theory bodyIntCallCompilerHash
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  builtinHashing compileEnv

Theorem intcall_interval_keccak256_word:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_keccak256_word v a))
Proof
  strip_tac >> simp[compile_keccak256_word_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_void, intcall_interval_emit_op])
QED

Theorem intcall_interval_keccak256_bytes:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_keccak256_bytes p a))
Proof
  strip_tac >> simp[compile_keccak256_bytes_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op])
QED

Theorem intcall_interval_keccak256_bytesm:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_keccak256_bytesm v m a))
Proof
  strip_tac >> simp[compile_keccak256_bytesm_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_void, intcall_interval_emit_op])
QED

Theorem intcall_interval_method_id_hash:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_method_id_hash ty v a))
Proof
  Cases_on `ty` >> simp[compile_method_id_hash_def,
    intcall_interval_keccak256_bytes] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_method_id_hash_def, intcall_interval_keccak256_bytes] >>
  rename1 `BytesT bnd` >> Cases_on `bnd` >>
  simp[compile_method_id_hash_def, intcall_interval_keccak256_bytes,
       intcall_interval_keccak256_bytesm]
QED

Theorem intcall_interval_method_id_runtime:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_method_id_runtime ty v b a))
Proof
  strip_tac >> Cases_on `b` >>
  simp[compile_method_id_runtime_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_method_id_hash, intcall_interval_alloc_buffer,
            intcall_interval_return, intcall_interval_emit_void,
            intcall_interval_emit_op])
QED

Theorem intcall_interval_sha256_word:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_sha256_word v a))
Proof
  strip_tac >> simp[compile_sha256_word_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_void, intcall_interval_emit_op])
QED

Theorem intcall_interval_sha256_bytes:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_sha256_bytes p a))
Proof
  strip_tac >> simp[compile_sha256_bytes_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_void, intcall_interval_emit_op])
QED

Theorem intcall_interval_sha256_bytesm:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_sha256_bytesm v m a))
Proof
  strip_tac >> simp[compile_sha256_bytesm_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_void, intcall_interval_emit_op])
QED
