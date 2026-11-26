(* Paired compiler boundary for the RHS of a local tuple assignment. *)
Theory s1PrefixAssignTupleLocalsCode
Ancestors
  tupleAssignParts tupleTargetStoreProps bodySimStmtFacts bodySim
  gasShadowCompileStmtHelpers gasShadowCompileBase gasShadowCompilePure
  gasShadow gasShadowState compileEnv exprLowering stmtLowering fragExec
  vyperAST vyperTypeSystem list

Theorem assign_tuple_rhs_code_segment[local]:
  stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e) sa = (c,sb) /\
  expr_type e = TupleT tys /\
  lowered_value_type cenv e = expr_type e /\
  cenv.ce_target CapMcopy /\ fn_has_code sa sb func ==>
  ?op su. lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
          fn_has_code sa su func
Proof
  strip_tac >>
  `(EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy)` by simp[] >>
  drule_all assign_tuple_targets_code_parts >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
    (qx_choosel_then [`vv`,`sc`,`op`,`su`,`staged`,`sl`,`elems`,`ss`] strip_assume_tac)) >>
  qexistsl_tac [`op`,`su`] >> simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su` by metis_tac[cs_extends_trans] >>
  `cs_extends su sb` by metis_tac[cs_extends_trans] >>
  irule (cj 1 fn_has_code_split) >> simp[] >> qexists_tac `sb` >> simp[]
QED

Theorem assign_tuple_locals_rhs_code:
  body_inv tops ctx cenv cx /\
  type_stmt env ret_ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
    SOME env' /\
  lowered_value_type cenv e = expr_type e /\
  stmt_env cenv lctx ret_ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
    sa = (c,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
    shadow_sa = (shadow_c,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?tys op su shadow_su.
    expr_type e = TupleT tys /\
    lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
    lower_value compile_expr (gas_shadow_env T cenv) (TupleT tys)
      (gas_shadow_expr e) shadow_sa = (op,shadow_su) /\
    gas_shadow_state su shadow_su /\
    fn_has_code sa su func /\ fn_has_code shadow_sa shadow_su shadow_func
Proof
  strip_tac >>
  drule tuple_targets_typing >> disch_then (qx_choose_then `tys` strip_assume_tac) >>
  drule_then assume_tac body_inv_mcopy >>
  drule_all assign_tuple_rhs_code_segment >>
  disch_then (qx_choosel_then [`op`,`su`] strip_assume_tac) >>
  `?shadow_op shadow_su.
      lower_value compile_expr (gas_shadow_env T cenv) (TupleT tys)
        (gas_shadow_expr e) shadow_sa = (shadow_op,shadow_su) /\
      fn_has_code shadow_sa shadow_su shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (Assign _ _) sa = _` kall_tac >>
     qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_stmt_def, gas_shadow_assignment_def] >> strip_tac >>
     `expr_type (gas_shadow_expr e) = TupleT tys` by simp[] >>
     `lowered_value_type (gas_shadow_env T cenv) (gas_shadow_expr e) =
        expr_type (gas_shadow_expr e)` by simp[] >>
     `(gas_shadow_env T cenv).ce_target CapMcopy` by simp[] >>
     drule_all assign_tuple_rhs_code_segment >> simp[]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (TupleT tys) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (TupleT tys) (gas_shadow_expr e))`
    by irule gas_shadow_stmt_lower_value_env >>
  pop_assum (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
  strip_tac >> qexistsl_tac [`tys`,`op`,`su`,`shadow_su`] >> simp[]
QED
