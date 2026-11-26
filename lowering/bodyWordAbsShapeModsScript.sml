(* Typing of Abs selects one signed-256 operand and enables its callback. *)
Theory bodyWordAbsShapeMods
Ancestors
  bodyFullPredsMods exprBodyPreProps exprSimHypsDefs
  vyperTypeSystem vyperInterpreter vyperContext vyperAST vyperTypeCallGraph
  supportedExprTraverse allocLimits compileEnv list

Theorem word_abs_shape_mods:
  (builtin_args_length_ok Abs (LENGTH args) ==>
     body_exprs_full_ok_mods mods exps cx args) /\
  expr_body_pre_mods mods cenv cx env (Builtin a Abs args) es ==>
  ?e. args = [e] /\ a = BaseT (IntT 256) /\ expr_type e = BaseT (IntT 256) /\
      expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e
Proof
  strip_tac >>
  `a = BaseT (IntT 256) /\ MAP expr_type args = [BaseT (IntT 256)]` by
    (drule expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def]) >>
  Cases_on `args` >> gvs[] >>
  `body_exprs_full_ok_mods mods exps cx [h]` by fs[builtin_args_length_ok_def] >>
  reverse conj_tac
  >- (qpat_x_assum `body_exprs_full_ok_mods _ _ _ [_]` mp_tac >>
      simp[Once body_exprs_full_ok_mods_def]) >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ Abs _) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM, constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED
