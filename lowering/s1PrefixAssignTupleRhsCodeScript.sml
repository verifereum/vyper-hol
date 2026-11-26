(* Common RHS code cut for tuple assignment and its gas shadow. *)
Theory s1PrefixAssignTupleRhsCode
Ancestors
  tupleAssignParts gasShadowCompileStmtHelpers gasShadowCompileBase
  gasShadow gasShadowState stmtLowering exprLowering compileEnv fragExec vyperAST list

Theorem assign_tuple_rhs_code_slices:
  stmt_env cenv lctx ty (Assign (TupleTarget gs) e) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ty
    (gas_shadow_stmt (Assign (TupleTarget gs) e)) shadow_sa =
      (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  expr_type e = TupleT tys /\
  lowered_value_type cenv e = expr_type e /\
  (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) ==>
  ?op su shadow_su.
    lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
    lower_value compile_expr (gas_shadow_env T cenv) (TupleT tys)
      (gas_shadow_expr e) shadow_sa = (op,shadow_su) /\
    gas_shadow_state su shadow_su /\
    fn_has_code sa su func /\
    fn_has_code shadow_sa shadow_su shadow_func
Proof
  strip_tac >>
  drule_all assign_tuple_targets_code_parts >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`vv`,`sc`,`op`,`su`,`staged`,`sl`,`elems`,`ss`]
      (map_every assume_tac o CONJUNCTS))) >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def,comp_bind_def] >>
  `fn_has_code sa su func` by
    (`cs_extends sa su /\ cs_extends su sb` by metis_tac[cs_extends_trans] >>
     metis_tac[fn_has_code_split]) >>
  `?shadow_su. lower_value compile_expr (gas_shadow_env T cenv) (TupleT tys)
      (gas_shadow_expr e) shadow_sa = (op,shadow_su) /\
      gas_shadow_state su shadow_su` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (TupleT tys) e)
        (lower_value compile_expr (gas_shadow_env T cenv) (TupleT tys) (gas_shadow_expr e))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (TupleT tys)
        (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `fn_has_code shadow_sa shadow_su shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_stmt_def,gas_shadow_assignment_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `expr_type (gas_shadow_expr e) = TupleT tys /\
       lowered_value_type (gas_shadow_env T cenv) (gas_shadow_expr e) =
         expr_type (gas_shadow_expr e)` by simp[] >>
     `(EXISTS (\t. ~is_word_type t) tys ==>
        (gas_shadow_env T cenv).ce_target CapMcopy)` by simp[] >>
     drule_all assign_tuple_targets_code_parts >>
     disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
       (qx_choosel_then [`svv`,`shadow_sc`,`sop`,`su2`,`sstaged`,`shadow_sl`,`selems`,`shadow_ss`]
         (map_every assume_tac o CONJUNCTS))) >>
     `op = sop /\ shadow_su = su2` by gvs[lower_value_def,comp_bind_def] >>
     `cs_extends shadow_sa su2 /\ cs_extends su2 shadow_sb` by metis_tac[cs_extends_trans] >>
     irule (cj 1 fn_has_code_split) >> conj_tac >- gvs[] >>
     qexists_tac `shadow_sb` >> gvs[]) >>
  qexistsl_tac [`op`,`su`,`shadow_su`] >> simp[]
QED
