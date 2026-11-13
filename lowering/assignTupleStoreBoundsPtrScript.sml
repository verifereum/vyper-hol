(* The target and its singleton write are genuine consecutive code slices. *)
Theory assignTupleStoreBoundsPtr
Ancestors stmtLoweringMono stmtLowering exprLoweringProps context compileEnv
  emitHelper emitHelperProps

Theorem tuple_singleton_target_bounds_ptr:
  compile_tuple_store_all cenv [sty] [BaseTarget bt] [op] sa = ((),sb) /\
  compile_get_target_ptr compile_expr cenv bt sa = ((dst,loc,pt),sm) ==>
  ci_mono sa sm /\ ci_mono sm sb
Proof
  strip_tac >> conj_tac
  >- metis_tac[ci_mono_compile_get_target_ptr,pairTheory.SND] >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [compile_tuple_store_all_def,comp_bind_def,
    comp_ignore_bind_def,comp_return_def,LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `is_word_type sty` >> gvs[]
  >- (Cases_on `is_word_type (case pt of SOME (ValPT t) => t | _ => sty)` >>
      gvs[] >> metis_tac[cj 2 ci_mono_stmt_helpers,ci_mono_emit_void,pairTheory.SND]) >>
  metis_tac[cj 1 ci_mono_stmt_helpers,pairTheory.SND]
QED
