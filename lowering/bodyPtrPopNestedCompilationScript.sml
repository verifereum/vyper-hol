Theory bodyPtrPopNestedCompilation
Ancestors bodyPtrPopBodyContext exprCallBounds stmtLoweringMono
  exprLoweringProps fragExec targetPlaceSimCases exprLowering compileEnv vyperAST

Theorem pop_target_callback_cong:
  !bt f g cenv.
    (!e. MEM e (target_indices bt) ==> !ce t st. f ce t e st = g ce t e st) ==>
    compile_get_target_ptr f cenv bt = compile_get_target_ptr g cenv bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_indices_def] >> rpt strip_tac
  >~ [`compile_get_target_ptr _ _ (NameTarget _)`]
  >- simp[compile_get_target_ptr_def]
  >~ [`compile_get_target_ptr _ _ (TopLevelNameTarget _)`]
  >- simp[compile_get_target_ptr_def] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  `compile_get_target_ptr f cenv b = compile_get_target_ptr g cenv b` by
    (first_x_assum irule >> metis_tac[]) >>
  pure_rewrite_tac[compile_get_target_ptr_def] >> asm_rewrite_tac[] >>
  `f cenv (expr_type e) e = g cenv (expr_type e) e` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  `lower_value f cenv (expr_type e) e = lower_value g cenv (expr_type e) e` by
    simp[lower_value_def, comp_bind_def, FUN_EQ_THM] >> asm_rewrite_tac[]
QED

Theorem pop_target_index_size:
  !bt e. MEM e (target_indices bt) ==> expr_size e < base_assignment_target_size bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_indices_def, expr_size_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  strip_tac >> res_tac >> decide_tac
QED

Theorem pop_target_guard_erasure:
  compile_get_target_ptr
    (expr_child_callback (expr_size (Pop ann bt)) f) cenv bt =
  compile_get_target_ptr f cenv bt
Proof
  irule pop_target_callback_cong >> rpt strip_tac >>
  irule expr_child_callback_valid >>
  drule pop_target_index_size >> simp[expr_size_def]
QED


Theorem pop_compile_target_decomposition:
  compile_get_target_ptr compile_expr cenv bt sa = ((hdr,lo,pt),sm) /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) ==>
  ?et q. (case pt of SOME (ValPT (ArrayT t sz)) => et = t
                       | _ => et = BaseT (IntT 256)) /\
    compile_dynarray_pop hdr (word_scale (case lo of SOME l => l | NONE => LocMemory))
      (elem_size_in_location cenv (case lo of SOME l => l | NONE => LocMemory) et)
      cenv.ce_is_ctor cenv.ce_imm_alloca
      (case lo of SOME l => l | NONE => LocMemory) sm = (q,sb) /\
    vv = LocatedValue ann (mk_ptr q (case lo of SOME l => l | NONE => LocMemory))
Proof
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       expr_type_def, SRULE [expr_size_def] pop_target_guard_erasure,
       SF ETA_ss] >>
  `compile_get_target_ptr
     (expr_child_callback (base_assignment_target_size bt + (type_size ann + 1)) compile_expr)
       cenv bt = compile_get_target_ptr compile_expr cenv bt` by
    (irule pop_target_callback_cong >> rpt strip_tac >>
     irule expr_child_callback_valid >> drule pop_target_index_size >> simp[]) >>
  asm_rewrite_tac[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `compile_dynarray_pop hdr ws esz ctor imm loc sm` >>
  Cases_on `compile_dynarray_pop hdr ws esz ctor imm loc sm` >> gvs[] >>
  unabbrev_all_tac >>
  Cases_on `pt` >> gvs[] >> Cases_on `x` >> gvs[] >>
  Cases_on `t` >> gvs[] >> metis_tac[]
QED

Theorem pop_compile_storage_suffix:
  compile_get_target_ptr compile_expr cenv bt sa =
    ((Var h,SOME (if tr then LocTransient else LocStorage),pt),sm) /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\ fn_has_code sa sb fn ==>
  ?et q. (case pt of SOME (ValPT (ArrayT t sz)) => et = t
                       | _ => et = BaseT (IntT 256)) /\
    compile_dynarray_pop (Var h) 1
      (elem_size_in_location cenv (if tr then LocTransient else LocStorage) et)
      cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage) sm = (q,sb) /\
    fn_has_code sm sb fn
Proof
  rpt strip_tac >> drule_all pop_compile_target_decomposition >> strip_tac >>
  `cs_extends sa sm` by
    (mp_tac (Q.SPECL [`bt`,`cenv`,`sa`] ci_mono_compile_get_target_ptr) >>
     simp[ci_mono_def]) >>
  `cs_extends sm sb` by
    (metis_tac[ci_mono_compile_dynarray_pop, ci_mono_def, pairTheory.SND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl_tac [`et`,`q`] >> Cases_on `tr` >> gvs[word_scale_def]
QED

Theorem pop_compile_storage_entry_exclusion:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  stmt_state_rel ctx fn cenv cx es s /\
  compile_get_target_ptr compile_expr cenv bt sa =
    ((Var h,SOME (if tr then LocTransient else LocStorage),pt),sm) /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  fn_has_code sa sb fn ==> F
Proof
  rpt strip_tac >> drule_all pop_compile_storage_suffix >> strip_tac >>
  drule_all pop_body_runtime_storage_exclusion >> simp[]
QED
