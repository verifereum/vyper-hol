(* Bare and unreachable assertions have no requests after their condition. *)
Theory s1PrefixAssertBare
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixOfVV stmtSimAssertProps
  gasShadowCompileStmtHelpers gasShadowState gasShadow exprLoweringProps
  bodyExprPreFacts stmtExprAllocationPreProps bodyInvCodeProps
  allocLimits allocLimitsProps compileUnit alist supportedStmts supportedExprs
  supportedExprTraverse supportedStmtTraverse vyperTypeSystem vyperTypeCallGraph
  loweringPosts vyperState bodySim

Theorem compile_assert_guard_frag_prefix:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (BaseT BoolT) e es ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Assert e ak))
    (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Assert e ak)))
    (eval_stmt cx (Assert e ak)) es
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `gas_shadow_assert_reason ak = ak` by
    (qpat_x_assum `_ \/ _` (DISJ_CASES_THEN SUBST_ALL_TAC) >> simp[gas_shadow_assert_reason_def]) >>
  pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  simp[gas_shadow_stmt_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Assert e _) sa = _`
    (mp_then Any mp_tac compile_assert_parts) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `lower_value compile_expr cenv (BaseT BoolT) e sa = (op,sm)` >>
  qpat_assum `stmt_env _ _ _ (Assert (gas_shadow_expr e) _) shadow_sa = _`
    (mp_then Any mp_tac compile_assert_parts) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `lower_value compile_expr _ _ (gas_shadow_expr e) shadow_sa = (sop,shadow_sm)` >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[compile_expr_grows] >>
  qpat_assum `cs_extends sa sm`
    (mp_then (Pos hd) mp_tac assert_compiler_code) >>
  disch_then (drule_all_then strip_assume_tac) >>
  qpat_assum `cs_extends shadow_sa shadow_sm`
    (mp_then (Pos hd) mp_tac assert_compiler_code) >>
  disch_then (drule_all_then strip_assume_tac) >>
  `op = sop /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (BaseT BoolT) e)
        (lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT) (gas_shadow_expr e))`
       by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `op = sop` (SUBST_ALL_TAC o SYM) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_expr_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                           `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  `!qe. SND (eval_stmt cx (Assert e ak) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (gen_tac >> drule eval_assert_bind >> disch_then (fn th => PURE_REWRITE_TAC [th]) >>
     Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >>
     simp[bind_def, raise_def, return_def] >> rpt IF_CASES_TAC >> simp[raise_def, return_def]) >>
  metis_tac[gas_prefix_full_state_cong]
QED

Theorem body_assert_guard_prefix_ok:
  !cx e ak. (ak = AssertBare \/ ak = AssertUnreachable) /\
    body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Assert e ak)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  pure_rewrite_tac[body_stmt_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def, supportedExprsTheory.supported_expr_def] >>
  `well_typed_expr env e /\ expr_type e = BaseT BoolT` by gvs[type_stmt_def] >>
  qpat_assum `body_inv tops ctx cenv cx`
    (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules
      o MATCH_MP body_inv_contract) >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`, `s` |-> `Assert e ak`]
       stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supported_stmt_expr_exists_def, supported_assert_exists_def] >>
     disch_then irule >>
     `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def] >>
     `~is_extcode e` by metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode] >>
     mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `calls` |-> `[]`]
       stmt_expr_body_pre_main_mods) >>
     qpat_x_assum `_ \/ _` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
     gvs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
         stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def, int_calls_assert_reason_def]) >>
  irule compile_assert_guard_frag_prefix >> simp[] >>
  qpat_x_assum `body_expr_prefix_ok cx e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
    `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `BaseT BoolT`, `es`] mp_tac) >>
  simp[]
QED
