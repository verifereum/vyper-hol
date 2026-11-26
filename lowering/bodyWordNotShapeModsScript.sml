(* The unary Not application supplies one typed, ready child. *)
Theory bodyWordNotShapeMods
Ancestors
  bodyFullPredsMods exprBodyPreProps exprSimHypsDefs exprSimUnopProps
  vyperTypeSystem vyperInterpreter vyperContext vyperAST vyperTypeCallGraph
  supportedExprTraverse allocLimits compileEnv list

Theorem word_not_shape_mods:
  builtin_args_length_ok Not (LENGTH args) /\
  body_exprs_full_ok_mods mods exps cx args /\
  expr_body_pre_mods mods cenv cx env (Builtin a Not args) es ==>
  ?e. args = [e] /\ a = expr_type e /\ is_word_type (expr_type e) /\
      expr_body_pre_mods mods cenv cx env e es /\
      body_expr_full_ok_mods mods exps cx e
Proof
  strip_tac >>
  `?e. args = [e]` by fs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  gvs[] >>
  `a = expr_type e /\ is_word_type (expr_type e)` by
    (drule expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def] >> strip_tac >>
     gvs[] >> qspec_then `expr_type e` mp_tac not_type_cases >>
     simp[] >> strip_tac >> simp[is_word_type_def]) >>
  gvs[] >>
  reverse conj_tac
  >- (qpat_x_assum `body_exprs_full_ok_mods _ _ _ [_]` mp_tac >>
      simp[Once body_expr_full_ok_mods_def]) >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ Not _) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM, constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED
