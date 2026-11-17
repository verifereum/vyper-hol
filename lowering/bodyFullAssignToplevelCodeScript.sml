(* Paired scalar top-level Assign compilation boundary. *)
Theory bodyFullAssignToplevelCode
Ancestors
  stmtSimAssignStorage gasShadowCompileStmtHelpers gasShadowState gasShadow
  stmtLowering exprLowering compileEnv vyperAST vyperTypeSystem

Theorem body_assign_toplevel_word_full_code:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) sa = (c,sf) /\
  stmt_env cenv lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) shadow_sa =
    (c,shadow_sf) /\
  FLOOKUP cenv.ce_module_vars nsid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_hashmap_info nsid = NONE /\ cenv.ce_module_var_type nsid = SOME vtyp /\
  is_word_type vtyp /\ is_word_type (expr_type e) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func ==>
  c = cenv /\
  ?op sb shadow_sb.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
    lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa =
      (op,shadow_sb) /\
    emit_void (if tr then TSTORE else SSTORE) [Lit slot;op] sb = ((),sf) /\
    cs_extends sa sb /\ cs_extends sb sf /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\ gas_shadow_state sb shadow_sb
Proof
  strip_tac >> drule_all assign_storage_word_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sb)` >>
  `?shadow_sb. lower_value compile_expr cenv (expr_type e)
       (gas_shadow_expr e) shadow_sa = (op,shadow_sb) /\
       gas_shadow_state sb shadow_sb` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
       gas_shadow_stmt_lower_value) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `fn_has_code shadow_sa shadow_sb shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `is_word_type (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
     drule_all assign_storage_word_code_parts >> strip_tac >>
     gvs[gas_shadow_expr_type] >> metis_tac[]) >>
  metis_tac[]
QED
