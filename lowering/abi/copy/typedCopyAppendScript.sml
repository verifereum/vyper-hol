(* TOP-LEVEL: all recursive typed memory-copy actions only append code,
   including branches that emit loops and branches that reject metadata. *)
Theory typedCopyAppend
Ancestors
  copyAppend context compileEnv emitHelper fragExec
  typedCopyDomain memoryLayoutDefs vyperAST list pair arithmetic
Libs BasicProvers

val typed_append_rules =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
   cs_appends_compile_copy_memory, cs_appends_compile_copy_memory_dynamic,
   cs_appends_compile_with_byte_offset, cs_appends_compile_store_bytestring];

fun typed_append_step goal = FIRST
  [CHANGED_TAC (asm_simp_tac (srw_ss()) typed_append_rules), gen_tac,
   irule cs_appends_bind >> conj_tac,
   irule cs_appends_ignore_bind >> conj_tac,
   IF_CASES_TAC, BasicProvers.TOP_CASE_TAC,
   first_assum (fn ih => irule (SRULE [ADD_COMM] ih) >> fs[ADD_COMM] >> NO_TAC)] goal;

Theorem cs_appends_typed_copy_mutual:
  (!cenv dst dst_ty src src_ty.
    cs_appends (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off.
    cs_appends (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_elem src src_elem count.
    cs_appends (compile_copy_sarray_typed cenv dst dst_elem src src_elem count)) /\
  (!cenv dst dst_elem capacity src src_elem.
    cs_appends (compile_copy_dynarray_typed cenv dst dst_elem capacity src src_elem)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off.
    cs_appends (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac >> rpt strip_tac >>
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM] >>
  NTAC 4 (TRY typed_append_step) >> NTAC 4 (TRY typed_append_step) >>
  rpt typed_append_step
QED

Theorem cs_appends_compile_store_memory:
  !cenv src dst dst_ty src_ty. cs_appends (compile_store_memory cenv src dst dst_ty src_ty)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_memory_def] >>
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss())
      (CONJUNCTS cs_appends_typed_copy_mutual @ typed_append_rules)), IF_CASES_TAC])
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive typed-copy append theorem: " ^ name)
  end) (DB.thms "typedCopyAppend")
