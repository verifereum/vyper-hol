(* TOP-LEVEL: continuation rules for the actual copy compiler's primitive
   actions. All emitted copy instructions have an opcode other than PHI. *)
Theory typedCopyCutRules
Ancestors
  typedCopyCut copyAppend typedCopyAppend context compileEnv emitHelper
  fragExec venomInst list

val cut_rules =
  [compiler_cut_continuation_return, compiler_cut_continuation_prims,
   compiler_cut_continuation_emit, compiler_cut_continuation_new_block,
   cs_appends_return, cs_appends_prims, cs_appends_emit_helpers];

fun cut_step rules = FIRST
  [CHANGED_TAC (asm_simp_tac (srw_ss()) (mk_inst_def :: rules)),
   gen_tac,
   irule compiler_cut_continuation_bind >> rpt conj_tac,
   irule compiler_cut_continuation_ignore_bind >> rpt conj_tac,
   irule cs_appends_bind >> rpt conj_tac,
   irule cs_appends_ignore_bind >> rpt conj_tac];

Theorem compiler_cut_continuation_emit_helpers:
  !opc. opc <> PHI ==>
    (!ops outs. compiler_cut_continuation (emit_inst opc ops outs)) /\
    (!ops. compiler_cut_continuation (emit_op opc ops)) /\
    (!ops. compiler_cut_continuation (emit_void opc ops))
Proof
  rpt gen_tac >> DISCH_TAC >>
  rw[emit_inst_def, emit_op_def, emit_void_def] >> rpt (cut_step cut_rules)
QED

val cut_emit_rules = compiler_cut_continuation_emit_helpers :: cut_rules;

Theorem compiler_cut_continuation_copy_memory:
  !dst src byte_count. compiler_cut_continuation (compile_copy_memory dst src byte_count)
Proof
  rpt gen_tac >> Cases_on `byte_count` >>
  simp[compile_copy_memory_def, compiler_cut_continuation_return, compiler_cut_continuation_emit_helpers]
QED

Theorem compiler_cut_continuation_copy_memory_dynamic:
  !dst src len_op. compiler_cut_continuation (compile_copy_memory_dynamic dst src len_op)
Proof
  simp[compile_copy_memory_dynamic_def, compiler_cut_continuation_emit_helpers]
QED

Theorem compiler_cut_continuation_with_byte_offset:
  !base_op offset. compiler_cut_continuation (compile_with_byte_offset base_op offset)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_with_byte_offset_def] >>
  IF_CASES_TAC >> simp[compiler_cut_continuation_return, compiler_cut_continuation_emit_helpers]
QED

Theorem compiler_cut_continuation_bytestring_copy_len:
  !src. compiler_cut_continuation (compile_bytestring_copy_len src)
Proof
  gen_tac >> simp_tac bool_ss [compile_bytestring_copy_len_def, LET_THM] >>
  rpt (cut_step cut_emit_rules)
QED

Theorem compiler_cut_continuation_store_bytestring:
  !src dst. compiler_cut_continuation (compile_store_bytestring src dst)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_bytestring_def] >>
  rpt (cut_step (compiler_cut_continuation_bytestring_copy_len ::
    compiler_cut_continuation_copy_memory_dynamic ::
    cs_appends_compile_bytestring_copy_len :: cs_appends_compile_copy_memory_dynamic :: cut_emit_rules))
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed copy compiler continuation rules: " ^ name)
  end) (DB.thms "typedCopyCutRules")
