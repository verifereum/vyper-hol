(* TOP-LEVEL: all five mutually recursive typed-copy compilers preserve
   instruction-ID history and grow the fresh counter. Recursive children
   therefore retain the code history established by their parents. *)
Theory typedCopyIdFlow
Ancestors
  compileIdFlow copyIdFlow context compileEnv emitHelper typedCopyDomain memoryLayoutDefs
  vyperAST list pair arithmetic
Libs BasicProvers

val typed_id_rules =
  [compiler_id_flow_return, compiler_id_flow_prims, compiler_id_flow_emit_helpers,
   compiler_id_flow_copy_memory, compiler_id_flow_copy_memory_dynamic,
   compiler_id_flow_with_byte_offset, compiler_id_flow_store_bytestring];

fun typed_id_step goal = FIRST
  [CHANGED_TAC (asm_simp_tac (srw_ss()) typed_id_rules), gen_tac,
   irule compiler_id_flow_bind >> conj_tac,
   irule compiler_id_flow_ignore_bind >> conj_tac,
   IF_CASES_TAC, BasicProvers.TOP_CASE_TAC,
   first_assum (fn ih => irule (SRULE [ADD_COMM] ih) >> fs[ADD_COMM] >> NO_TAC)] goal;

Theorem compiler_id_flow_typed_copy:
  (!cenv dst dst_ty src src_ty.
    compiler_id_flow (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off.
    compiler_id_flow (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_elem src src_elem copy_count.
    compiler_id_flow (compile_copy_sarray_typed cenv dst dst_elem src src_elem copy_count)) /\
  (!cenv dst dst_elem capacity src src_elem.
    compiler_id_flow (compile_copy_dynarray_typed cenv dst dst_elem capacity src src_elem)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off.
    compiler_id_flow (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac >> rpt strip_tac >>
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM] >>
  (* FIRST [...] makes holbuild time each block once per goal. *)
  FIRST [NTAC 2 (TRY typed_id_step)] >> FIRST [NTAC 2 (TRY typed_id_step)] >>
  FIRST [NTAC 2 (TRY typed_id_step)] >> FIRST [NTAC 2 (TRY typed_id_step)] >>
  FIRST [rpt typed_id_step]
QED

Theorem compile_store_memory_typed_next_id:
  !cenv dst dst_ty src src_ty cs ret cs'.
    compile_store_memory_typed cenv dst dst_ty src src_ty cs = (ret,cs') ==>
    cs.cs_next_id <= cs'.cs_next_id
Proof
  rpt gen_tac >> DISCH_TAC >>
  `compiler_id_flow (compile_store_memory_typed cenv dst dst_ty src src_ty)` by
    simp[CONJUNCT1 compiler_id_flow_typed_copy] >>
  drule_all compiler_id_flow_result >> simp[]
QED

Theorem compiler_id_flow_store_memory:
  !cenv src dst dst_ty src_ty. compiler_id_flow (compile_store_memory cenv src dst dst_ty src_ty)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_memory_def] >>
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss())
    (CONJUNCTS compiler_id_flow_typed_copy @ typed_id_rules)), IF_CASES_TAC])
QED
