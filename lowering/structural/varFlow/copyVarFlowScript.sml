(* TOP-LEVEL: primitive memory-copy compilation preserves the monotonic
   generated-name counter, including zero-sized copies and buffer allocation. *)
Theory copyVarFlow
Ancestors
  compileVarFlow context compileEnv emitHelper list

val copy_var_rules =
  [compiler_vars_mono_return, compiler_vars_mono_prims, compiler_vars_mono_emit_helpers];

fun copy_var_tac rules = rpt (FIRST
  [CHANGED_TAC (asm_simp_tac (srw_ss()) rules),
   irule compiler_vars_mono_bind >> conj_tac >> rpt gen_tac,
   irule compiler_vars_mono_ignore_bind >> conj_tac, IF_CASES_TAC]);

Theorem compiler_vars_mono_copy_memory:
  !dst src byte_count. compiler_vars_mono (compile_copy_memory dst src byte_count)
Proof
  rpt gen_tac >> Cases_on `byte_count` >>
  simp[compile_copy_memory_def, compiler_vars_mono_return, compiler_vars_mono_emit_helpers]
QED

Theorem compiler_vars_mono_copy_memory_dynamic:
  !dst src len_op. compiler_vars_mono (compile_copy_memory_dynamic dst src len_op)
Proof
  simp[compile_copy_memory_dynamic_def, compiler_vars_mono_emit_helpers]
QED

Theorem compiler_vars_mono_with_byte_offset:
  !ptr offset. compiler_vars_mono (compile_with_byte_offset ptr offset)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_with_byte_offset_def] >> copy_var_tac copy_var_rules
QED

Theorem compiler_vars_mono_bytestring_copy_len:
  !src. compiler_vars_mono (compile_bytestring_copy_len src)
Proof
  gen_tac >> simp_tac bool_ss [compile_bytestring_copy_len_def, LET_THM] >> copy_var_tac copy_var_rules
QED

Theorem compiler_vars_mono_store_bytestring:
  !src dst. compiler_vars_mono (compile_store_bytestring src dst)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_bytestring_def] >>
  copy_var_tac (compiler_vars_mono_bytestring_copy_len :: copy_var_rules)
QED

Theorem compiler_vars_mono_alloc_buffer:
  !byte_count. compiler_vars_mono (compile_alloc_buffer byte_count)
Proof
  gen_tac >> simp_tac bool_ss [compile_alloc_buffer_def] >> copy_var_tac copy_var_rules
QED
