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

(* One deterministic split of a goal `cs_appends m`, chosen by m's head:
   a bind or a sequencing step becomes its two halves, a conditional its two
   branches. Any other head (a primitive, a recursive call, a case) fails. *)
fun append_split_tac (g as (_, w)) =
  let val m = rand w
  in
    if is_cond m then IF_CASES_TAC g
    else case total (fst o dest_const o fst o strip_comb) m of
        SOME "comp_bind" =>
          (irule cs_appends_bind >> conj_tac >> rpt gen_tac >> BETA_TAC) g
      | SOME "comp_ignore_bind" => (irule cs_appends_ignore_bind >> conj_tac) g
      | _ => NO_TAC g
  end;

(* Case split on the variable that a goal `cs_appends (case x of ...)`
   dispatches on; fails on any other goal. *)
fun append_case_tac (g as (_, w)) =
  let val (_, x, _) = TypeBase.dest_case (rand w)
  in if is_var x then Cases_on `^x` g else NO_TAC g end
  handle HOL_ERR _ => NO_TAC g;

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
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM]
  >~ [`ALOOKUP src_fields name`]
  >- (pairarg_tac >>
      pop_assum (fn th => assume_tac th >> pure_rewrite_tac [th, pairTheory.UNCURRY_DEF]) >>
      BETA_TAC >> rpt append_split_tac >> simp_tac bool_ss typed_append_rules >>
      first_x_assum irule >> simp[])
  >~ [`emit_void INVALID []`]
  >- (rpt append_split_tac >> simp_tac bool_ss typed_append_rules >>
      Cases_on `src_ty` >> simp_tac (srw_ss()) [cs_appends_compile_copy_memory] >>
      Cases_on `dst_ty` >> simp_tac (srw_ss()) [cs_appends_compile_copy_memory] >>
      rpt (append_case_tac >> simp_tac (srw_ss()) [cs_appends_compile_copy_memory]) >>
      first_x_assum irule >> fs[]) >>
  rpt append_split_tac >> simp_tac bool_ss typed_append_rules >>
  first_x_assum irule >> fs[]
QED

Theorem cs_appends_compile_store_memory:
  !cenv src dst dst_ty src_ty. cs_appends (compile_store_memory cenv src dst dst_ty src_ty)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_memory_def] >>
  rpt append_split_tac >>
  simp_tac bool_ss (CONJUNCTS cs_appends_typed_copy_mutual @ typed_append_rules)
QED
