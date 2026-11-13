(*
 * The control cases of bodySimFullMain's induction, at bodyFullPreds's
 * joint judgments: Break, Continue, the bare and unreachable Raise and
 * Assert, If, the expression statement and a statement list's cons.
 * Each is its joint fragment (bodyFullExits, bodyFullIf, bodyFullExprStmt,
 * bodyFullStmtsCons) with the premises discharged from the case's
 * invariants, as the S1 cases of bodySimStmtCases do; bodyFullCases
 * closes its cases with them.
 *
 * TOP-LEVEL:
 *   break_stmt_full_ok, continue_stmt_full_ok,
 *   raise_bare_stmt_full_ok, raise_unreachable_stmt_full_ok,
 *   assert_bare_stmt_full_ok, assert_unreachable_stmt_full_ok,
 *   if_stmt_full_ok, expr_stmt_full_ok, stmts_cons_full_ok
 *)
Theory bodyFullCtrlCases
Ancestors
  bodyFullPreds bodyFullExits bodyFullIf bodyFullExprStmt bodyFullStmtsCons
  bodySimFull bodyExprPreFacts exprOpenMain exprSimSource
  gasShadowCompileStmt gasShadowCompileStmtHelpers gasShadowCompileStmtBase
  gasShadowState gasShadow stmtSimProps loweringPosts stmtLoweringMono
  exprLoweringProps supportedStmts supportedExprs supportedStmtTraverse
  supportedExprTraverse exprSimHypsDefs bodySim gasContext
  vyperTypeCallStackSoundness vyperTypeSystem vyperTypeCallGraph
  compileEnv vyperInterpreter vyperState vyperAST list

val _ = Parse.hide "body";

(* ===== Exits ===== *)

Theorem break_stmt_full_ok:
  !cx. body_stmt_full_ok cx Break
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def] >>
  irule compile_loop_jump_frag_full >> simp[]
QED

Theorem continue_stmt_full_ok:
  !cx. body_stmt_full_ok cx Continue
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def] >>
  irule compile_loop_jump_frag_full >> simp[]
QED

Theorem raise_bare_stmt_full_ok:
  !cx. body_stmt_full_ok cx (Raise RaiseBare)
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  irule compile_raise_frag_full >> simp[]
QED

Theorem raise_unreachable_stmt_full_ok:
  !cx. body_stmt_full_ok cx (Raise RaiseUnreachable)
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  irule compile_raise_frag_full >> simp[]
QED

(* An assertion with no reason: the condition's joint simulation at
   BaseT BoolT, by its case at the expr_body_pre its statement gives. *)
Theorem body_assert_bare_full[local]:
  !cx e ak.
    (ak = AssertBare \/ ak = AssertUnreachable) /\ body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assert e ak)
Proof
  rpt gen_tac >> strip_tac >>
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def, gas_shadow_assert_reason_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `well_typed_expr env e /\ expr_type e = BaseT BoolT` by gvs[type_stmt_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag_full >> simp[] >>
  qpat_x_assum `body_expr_full_ok _ _`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_full_ok_def]) >>
  disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`, `shadow_ctx`,
    `func`, `shadow_func`, `cenv`, `env`, `BaseT BoolT`, `es`] mp_tac) >>
  simp[]
QED

Theorem assert_bare_stmt_full_ok:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Assert e AssertBare)
Proof
  metis_tac[body_assert_bare_full]
QED

Theorem assert_unreachable_stmt_full_ok:
  !cx e.
    body_expr_full_ok cx e ==> body_stmt_full_ok cx (Assert e AssertUnreachable)
Proof
  metis_tac[body_assert_bare_full]
QED

(* ===== The expression statement ===== *)

Theorem expr_stmt_full_ok:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Expr e)
Proof
  rpt gen_tac >> strip_tac >>
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         int_calls_stmt_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_expr_stmt_frag_ok_full >>
  simp[gas_shadow_stmt_compile_expr] >> conj_tac
  >- (rpt strip_tac >>
      `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
      metis_tac[compile_expr_open_general]) >>
  qpat_x_assum `body_expr_full_ok _ _`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_full_ok_def]) >>
  disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`, `shadow_ctx`,
    `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`] mp_tac) >>
  simp[]
QED

(* ===== If ===== *)

(* A block's compile environment pairs with its shadow's. *)
Theorem if_branch_shadow_compiles[local]:
  !ss cenv lctx ty.
    gas_shadow_compiles (stmts_env cenv lctx ty ss)
      (stmts_env cenv lctx ty (MAP gas_shadow_stmt ss))
Proof
  Induct >> simp[stmts_env_def, gas_shadow_compiles_return] >>
  rpt gen_tac >> ho_match_mp_tac gas_shadow_compiles_get_terminated >>
  Cases >> simp[gas_shadow_compiles_return] >>
  irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_declare_stmt_local] >> gen_tac >>
  simp[comp_ignore_bind_def] >> irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compile_stmt]
QED

Theorem if_stmt_full_ok:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss2) /\ body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (If e ss1 ss2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_stmt_full_ok_def, gas_shadow_stmt_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
      supported_stmt_expr_exists_def, DE_MORGAN_THM]) >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre_alloc >> gvs[body_inv_def] >>
     qexists_tac `int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cenv cx (BaseT BoolT) e es` by
    (qpat_x_assum `body_expr_full_ok _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
       `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `BaseT BoolT`,
       `es`] mp_tac) >> simp[]) >>
  irule compile_if_stmt_frag_full >>
  simp[stmts_env_cs_mono, gas_shadow_stmt_lower_value,
       if_branch_shadow_compiles] >>
  conj_tac >- metis_tac[compile_expr_grows] >>
  conj_tac >- metis_tac[compile_expr_grows] >>
  rpt strip_tac >>
  rename1 `_ = (INL (BoolV b), es1)` >>
  `?tv s1. eval_expr cx e (es with gas_obs := gs) = (INL tv, s1)` by
    (qpat_x_assum `_ = (INL (BoolV b), es1)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_stmts_full_ok cx ss1 /\ body_stmts_full_ok cx ss2` by
    (`push_scope es1 = (INL (), es1 with scopes updated_by CONS FEMPTY)` by
       simp[push_scope_def, return_def] >>
     metis_tac[]) >>
  `expr_sim_inv cenv cx env es1` by
    (`expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
     drule exprSimSourceTheory.expr_body_pre_eval >>
     disch_then (qspecl_then [`INL (BoolV b)`, `es1`] mp_tac) >>
     impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  drule expr_sim_inv_push_scope >> strip_tac >>
  rpt (qpat_x_assum `body_stmts_full_ok _ _`
         (strip_assume_tac o REWRITE_RULE [body_stmts_full_ok_def])) >>
  Cases_on `b` >> fs[] >> first_x_assum irule >>
  gvs[stmts_exprs_ok_thm, stmt_exprs_ok_def,
      allocLimitsTheory.alloc_limits_stmt_def,
      compileVyperTheory.stmt_valued_return_def,
      GSYM optionTheory.IS_SOME_EXISTS] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

(* ===== Statement lists ===== *)

(* The head by its case; the tail by the IH at the environments the
   head's typing and declaration give. *)
Theorem stmts_cons_full_ok:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_full_ok cx ss) /\
    body_stmt_full_ok cx s ==>
    body_stmts_full_ok cx (s::ss)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmts_full_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, AllCaseEqs(), int_calls_stmt_def,
      supported_stmt_expr_exists_def] >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  irule (REWRITE_RULE [MAP] stmt_frag_full_cons_env) >> reverse conj_tac
  >- (qpat_x_assum `body_stmt_full_ok _ _`
        (irule o REWRITE_RULE [body_stmt_full_ok_def]) >>
      metis_tac[call_evaluation_safe_append_left]) >>
  rpt strip_tac >>
  rename1 `stmt_env cenv lctx ret_ty s sa = (c, sm)` >>
  `same_frame cenv c` by metis_tac[cenv_top_ext_same_frame] >>
  `stmts_exprs_ok c = stmts_exprs_ok (decl_var_type cenv s)` by
    metis_tac[stmt_env_stmts_exprs_ok] >>
  `expr_sim_inv c cx env1 es1` by
    (irule expr_sim_inv_stmt >> fs[body_inv_def] >>
     metis_tac[expr_sim_inv_gas_obs, call_evaluation_safe_append_left]) >>
  `ce_locals_declared c env1` by metis_tac[ce_locals_declared_stmt] >>
  `locals_alloc_ok c env1` by metis_tac[locals_alloc_ok_stmt] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cx RetQ c ret_ty` by
    (qpat_x_assum `frame_ret_ok_full _ _ _ _ _` mp_tac >>
     rewrite_tac[frame_ret_ok_full_def] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[same_frame_trans]) >>
  qpat_x_assum `!s'' t. _ ==> body_stmts_full_ok _ _` drule >>
  simp[body_stmts_full_ok_def] >> disch_then irule >>
  metis_tac[call_evaluation_safe_append_right]
QED
