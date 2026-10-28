(* TOP-LEVEL: every actual recursive typed copy transports continuation
   no-PHI facts backwards through its containing code. This discharges
   the intermediate continuation obligations of sequential field copies. *)
Theory typedCopyContinuations
Ancestors
  typedCopyCut typedCopyCutRules typedCopyAppend copyAppend context compileEnv emitHelper
  fragExec typedCopyDomain memoryLayoutDefs vyperAST list pair arithmetic
Libs
  BasicProvers

val typed_cut_rules =
  [compiler_cut_continuation_return, compiler_cut_continuation_prims,
   compiler_cut_continuation_emit_helpers, compiler_cut_continuation_new_block,
   compiler_cut_continuation_copy_memory, compiler_cut_continuation_copy_memory_dynamic,
   compiler_cut_continuation_with_byte_offset, compiler_cut_continuation_store_bytestring,
   cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
   cs_appends_compile_copy_memory, cs_appends_compile_copy_memory_dynamic,
   cs_appends_compile_with_byte_offset, cs_appends_compile_store_bytestring] @
  CONJUNCTS cs_appends_typed_copy_mutual;

fun typed_cut_step goal = FIRST
  [CHANGED_TAC (simp_tac (srw_ss()) typed_cut_rules),
   CHANGED_TAC (asm_simp_tac (srw_ss()) typed_cut_rules), gen_tac,
   irule compiler_cut_continuation_bind >> rpt conj_tac,
   irule compiler_cut_continuation_ignore_bind >> rpt conj_tac,
   irule cs_appends_bind >> rpt conj_tac,
   irule cs_appends_ignore_bind >> rpt conj_tac,
   IF_CASES_TAC, BasicProvers.TOP_CASE_TAC,
   first_assum (fn ih => irule (SRULE [ADD_COMM] ih) >> fs[ADD_COMM] >> NO_TAC)] goal;

Theorem compiler_cut_continuation_typed_copy_mutual:
  (!cenv dst dst_ty src src_ty.
    compiler_cut_continuation (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off.
    compiler_cut_continuation (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_elem src src_elem count.
    compiler_cut_continuation (compile_copy_sarray_typed cenv dst dst_elem src src_elem count)) /\
  (!cenv dst dst_elem capacity src src_elem.
    compiler_cut_continuation (compile_copy_dynarray_typed cenv dst dst_elem capacity src src_elem)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off.
    compiler_cut_continuation (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac >> rpt strip_tac >>
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM] >>
  NTAC 2 (TRY typed_cut_step) >> NTAC 2 (TRY typed_cut_step) >>
  NTAC 2 (TRY typed_cut_step) >> NTAC 2 (TRY typed_cut_step) >> rpt typed_cut_step
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive typed-copy continuation facts: " ^ name)
  end) (DB.thms "typedCopyContinuations")
