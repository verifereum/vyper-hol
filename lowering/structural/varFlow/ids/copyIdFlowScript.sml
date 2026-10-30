(* TOP-LEVEL: primitive memory-copy compilation preserves instruction-ID
   freshness and grows the ID counter, including allocation and empty copies. *)
Theory copyIdFlow
Ancestors
  compileIdFlow context compileEnv emitHelper list

val copy_id_rules =
  [compiler_id_flow_return, compiler_id_flow_prims, compiler_id_flow_emit_helpers];

fun copy_id_tac rules = rpt (FIRST
  [CHANGED_TAC (asm_simp_tac (srw_ss()) rules),
   irule compiler_id_flow_bind >> conj_tac >> rpt gen_tac,
   irule compiler_id_flow_ignore_bind >> conj_tac, IF_CASES_TAC]);

Theorem compiler_id_flow_copy_memory:
  !dst src byte_count. compiler_id_flow (compile_copy_memory dst src byte_count)
Proof
  rpt gen_tac >> Cases_on `byte_count` >>
  simp[compile_copy_memory_def, compiler_id_flow_return, compiler_id_flow_emit_helpers]
QED

Theorem compiler_id_flow_copy_memory_dynamic:
  !dst src len_op. compiler_id_flow (compile_copy_memory_dynamic dst src len_op)
Proof
  simp[compile_copy_memory_dynamic_def, compiler_id_flow_emit_helpers]
QED

Theorem compiler_id_flow_with_byte_offset:
  !ptr offset. compiler_id_flow (compile_with_byte_offset ptr offset)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_with_byte_offset_def] >> copy_id_tac copy_id_rules
QED

Theorem compiler_id_flow_bytestring_copy_len:
  !src. compiler_id_flow (compile_bytestring_copy_len src)
Proof
  gen_tac >> simp_tac bool_ss [compile_bytestring_copy_len_def, LET_THM] >> copy_id_tac copy_id_rules
QED

Theorem compiler_id_flow_store_bytestring:
  !src dst. compiler_id_flow (compile_store_bytestring src dst)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_bytestring_def] >>
  copy_id_tac (compiler_id_flow_bytestring_copy_len :: copy_id_rules)
QED

Theorem compiler_id_flow_alloc_buffer:
  !byte_count. compiler_id_flow (compile_alloc_buffer byte_count)
Proof
  gen_tac >> simp_tac bool_ss [compile_alloc_buffer_def] >> copy_id_tac copy_id_rules
QED
