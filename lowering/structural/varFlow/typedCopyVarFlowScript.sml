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

(* Split only the outer conditional, bind or sequencing operation. *)
fun var_split_tac (g as (_, w)) =
  let val m = rand w
  in
    if is_cond m then IF_CASES_TAC g
    else case total (fst o dest_const o fst o strip_comb) m of
        SOME "comp_bind" =>
          (irule compiler_vars_mono_bind >> conj_tac >> rpt gen_tac >> BETA_TAC) g
      | SOME "comp_ignore_bind" =>
          (irule compiler_vars_mono_ignore_bind >> conj_tac) g
      | _ => NO_TAC g
  end;

fun var_case_tac (g as (_, w)) =
  let val (_, x, _) = TypeBase.dest_case (rand w)
  in if is_var x then Cases_on `^x` g else NO_TAC g end
  handle HOL_ERR _ => NO_TAC g;

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
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM]
  >~ [`ALOOKUP src_fields name`]
  >- (pairarg_tac >>
      pop_assum (fn th => assume_tac th >> pure_rewrite_tac [th, pairTheory.UNCURRY_DEF]) >>
      BETA_TAC >> rpt var_split_tac >> simp_tac bool_ss typed_var_rules >>
      first_x_assum irule >> simp[])
  >~ [`emit_void INVALID []`]
  >- (rpt var_split_tac >> simp_tac bool_ss typed_var_rules >>
      Cases_on `src_ty` >> simp_tac (srw_ss()) [compiler_vars_mono_copy_memory] >>
      Cases_on `dst_ty` >> simp_tac (srw_ss()) [compiler_vars_mono_copy_memory] >>
      rpt (var_case_tac >> simp_tac (srw_ss()) [compiler_vars_mono_copy_memory]) >>
      first_x_assum irule >> fs[]) >>
  rpt var_split_tac >> simp_tac bool_ss typed_var_rules >>
  first_x_assum irule >> fs[]
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
  rpt var_split_tac >>
  simp_tac bool_ss (CONJUNCTS compiler_vars_mono_typed_copy @ typed_var_rules)
QED
