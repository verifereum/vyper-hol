(* TOP-LEVEL: all five mutually recursive typed-copy compilers allocate
   variable names monotonically. This holds for every input and prevents
   a recursive child from reusing names already reserved by its parent. *)
Theory typedCopyVarFlow
Ancestors
  compileVarFlow copyVarFlow context compileEnv emitHelper typedCopyDomain memoryLayoutDefs
  vyperAST list pair arithmetic
Libs BasicProvers

val typed_var_rules =
  [compiler_vars_mono_return, compiler_vars_mono_prims, compiler_vars_mono_emit_helpers,
   compiler_vars_mono_copy_memory, compiler_vars_mono_copy_memory_dynamic,
   compiler_vars_mono_with_byte_offset, compiler_vars_mono_store_bytestring];

fun typed_var_step goal = FIRST
  [CHANGED_TAC (simp_tac (srw_ss()) typed_var_rules), gen_tac,
   irule compiler_vars_mono_bind >> conj_tac >> rpt gen_tac,
   irule compiler_vars_mono_ignore_bind >> conj_tac,
   IF_CASES_TAC,
   BasicProvers.PURE_TOP_CASE_TAC >> simp_tac (srw_ss()) typed_var_rules,
   first_assum (fn ih => irule ih >> fs[] >> NO_TAC)] goal;

Theorem compiler_vars_mono_typed_copy:
  (!cenv dst dst_ty src src_ty.
    compiler_vars_mono (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off.
    compiler_vars_mono (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_elem src src_elem copy_count.
    compiler_vars_mono (compile_copy_sarray_typed cenv dst dst_elem src src_elem copy_count)) /\
  (!cenv dst dst_elem capacity src src_elem.
    compiler_vars_mono (compile_copy_dynarray_typed cenv dst dst_elem capacity src src_elem)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off.
    compiler_vars_mono (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac >> rpt strip_tac >>
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM] >>
  rpt typed_var_step
QED

Theorem compile_store_memory_typed_next_var:
  !cenv dst dst_ty src src_ty cs ret cs'.
    compile_store_memory_typed cenv dst dst_ty src src_ty cs = (ret,cs') ==>
    cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >>
  `compiler_vars_mono (compile_store_memory_typed cenv dst dst_ty src src_ty)` by
    simp[CONJUNCT1 compiler_vars_mono_typed_copy] >>
  drule_all compiler_vars_mono_result >> simp[]
QED

Theorem compiler_vars_mono_store_memory:
  !cenv src dst dst_ty src_ty. compiler_vars_mono (compile_store_memory cenv src dst dst_ty src_ty)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_memory_def] >>
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss())
    (CONJUNCTS compiler_vars_mono_typed_copy @ typed_var_rules)), IF_CASES_TAC])
QED
