(* TOP-LEVEL: the primitive memory-copy compiler actions only append code.
   These facts preserve actual function containment when stores compose. *)
Theory copyAppend
Ancestors
  context compileEnv emitHelper fragExec list

val copy_append_rules = [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers];

fun copy_append_tac rules =
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss()) rules),
    irule cs_appends_bind >> conj_tac >> rpt gen_tac,
    irule cs_appends_ignore_bind >> conj_tac,
    IF_CASES_TAC]);

Theorem cs_appends_compile_copy_memory:
  !dst src byte_count. cs_appends (compile_copy_memory dst src byte_count)
Proof
  rpt gen_tac >> Cases_on `byte_count` >>
  simp[compile_copy_memory_def, cs_appends_return, cs_appends_emit_helpers]
QED

Theorem cs_appends_compile_copy_memory_dynamic:
  !dst src len_op. cs_appends (compile_copy_memory_dynamic dst src len_op)
Proof
  simp[compile_copy_memory_dynamic_def, cs_appends_emit_helpers]
QED

Theorem cs_appends_compile_with_byte_offset:
  !ptr offset. cs_appends (compile_with_byte_offset ptr offset)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_with_byte_offset_def] >>
  copy_append_tac copy_append_rules
QED

Theorem cs_appends_compile_bytestring_copy_len:
  !src. cs_appends (compile_bytestring_copy_len src)
Proof
  gen_tac >> simp_tac bool_ss [compile_bytestring_copy_len_def, LET_THM] >>
  copy_append_tac copy_append_rules
QED

Theorem cs_appends_compile_store_bytestring:
  !src dst. cs_appends (compile_store_bytestring src dst)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_bytestring_def] >>
  copy_append_tac (cs_appends_compile_bytestring_copy_len :: copy_append_rules)
QED

Theorem cs_appends_compile_alloc_buffer:
  !byte_count. cs_appends (compile_alloc_buffer byte_count)
Proof
  gen_tac >> simp_tac bool_ss [compile_alloc_buffer_def] >> copy_append_tac copy_append_rules
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed memory-copy append theorem: " ^ name)
  end) (DB.thms "copyAppend")
