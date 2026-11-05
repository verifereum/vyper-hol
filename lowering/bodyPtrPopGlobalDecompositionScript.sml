Theory bodyPtrPopGlobalDecomposition
Ancestors
  bodyPtrPopGlobalLoweringInputs bodyPtrPopGlobalLegality exprLoweringProps
  exprLowering compileEnv context bodyPtrPopIndexDecomposition
  bodyPtrPopGuardNormalization vyperAST

Theorem pop_global_call_decomposition:
  !ret_ty sa vv sb.
    compile_expr pop_global_package_env ret_ty
      (Pop (BaseT (UintT 256)) pop_global_target) sa = (vv,sb) ==>
    ?sc sd cv.
      cs_extends sa sc /\
      compile_call compile_expr pop_global_package_env
        (BaseT (UintT 256)) (BaseT (UintT 256))
        (IntCall (NONE,"replace")) [] NONE sc = (cv,sd) /\
      cs_extends sc sd /\ cs_extends sd sb
Proof
  rpt gen_tac >>
  simp[Once compile_expr_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  `!ce ty e s. ci_mono s
     (SND (expr_child_callback
       (base_assignment_target_size pop_global_target + 259)
       compile_expr ce ty e s))` by
    (irule ci_mono_expr_child_callback >>
     simp[cj 1 compile_expr_ci_mono]) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[pop_global_target_def] >>
  strip_tac >>
  qpat_x_assum `!ce ty e s. _` (assume_tac o PURE_REWRITE_RULE [pop_global_target_def]) >>
  drule_all pop_subscript_index_decomposition >>
  strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE
    [GSYM pop_global_target_def, expr_type_def, pop_global_replace_guard]) >>
  `ci_mono st1 sb` by
    metis_tac[ci_mono_compile_dynarray_pop, pairTheory.SND] >>
  qexistsl_tac [`sc`,`sd`,`cv`] >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED
