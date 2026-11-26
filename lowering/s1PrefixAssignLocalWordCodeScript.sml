(* Ordinary and shadow RHS code intervals for a word-local assignment. *)
Theory s1PrefixAssignLocalWordCode
Ancestors
  stmtSimAssign gasShadowCompileStmtHelpers gasShadowState gasShadow
  stmtLowering exprLowering compileEnv vyperAST finite_map

Theorem assign_local_word_rhs_code_pair:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (c,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)) shadow_sa =
    (sc,shadow_sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (expr_type e) /\
  is_word_type (expr_type e) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?op sm shadow_sm.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\
    fn_has_code sa sm func /\
    fn_has_code shadow_sa shadow_sm shadow_func
Proof
  strip_tac >> drule_all assign_local_word_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
     (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`,
                     `sd` |-> `T`] gas_shadow_stmt_lower_value_env) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `is_word_type (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
     `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) sz)` by simp[] >>
     `(gas_shadow_env T cenv).ce_var_type id = SOME (expr_type (gas_shadow_expr e))` by
       simp[gas_shadow_expr_type] >>
     drule_all assign_local_word_code_parts >> strip_tac >> gvs[gas_shadow_expr_type] >>
     metis_tac[]) >>
  metis_tac[]
QED
