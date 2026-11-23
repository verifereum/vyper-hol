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
  bodyInvExecutionProps
  bodyFullPreds bodyFullExits bodyFullExitActions bodyFullIf bodyFullExprStmt bodyFullStmtsCons
  bodyFullIfExpReach
  bodySimFull bodyExprPreFacts exprOpenMain exprSimSource
  gasShadowCompileStmt gasShadowCompileStmtHelpers gasShadowCompileStmtBase
  gasShadowStmtEnv
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
  irule compile_loop_jump_frag_full_action >> simp[]
QED

Theorem continue_stmt_full_ok:
  !cx. body_stmt_full_ok cx Continue
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def] >>
  irule compile_loop_jump_frag_full_action >> simp[]
QED

Theorem raise_bare_stmt_full_ok:
  !cx. body_stmt_full_ok cx (Raise RaiseBare)
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  irule compile_raise_frag_full_action >> simp[]
QED

Theorem raise_unreachable_stmt_full_ok:
  !cx. body_stmt_full_ok cx (Raise RaiseUnreachable)
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  irule compile_raise_frag_full_action >> simp[]
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
  `well_typed_expr env e /\ expr_type e = BaseT BoolT` by gvs[type_stmt_def] >>
  qpat_assum `body_inv tops ctx cenv cx`
    (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules
      o MATCH_MP body_inv_contract) >>
  `expr_body_pre cenv cx env e es` by
    (qpat_assum `stmt_exprs_ok cenv (Assert e _)` (fn ok =>
       mp_tac (INST [Term `s:stmt` |-> rand (concl ok)]
         (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`]
           stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton))) >>
     simp[supported_stmt_expr_exists_def, supported_assert_exists_def, int_calls_stmt_def, int_calls_assert_reason_def] >>
     disch_then irule >>
     `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def] >>
     `~is_extcode e` by metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode] >>
     mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `calls` |-> `[]`]
              stmt_expr_body_pre_main_mods) >>
     gvs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
         stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def, int_calls_assert_reason_def]) >>
  irule compile_assert_frag_full >> simp[] >>
  qpat_x_assum `body_expr_full_ok _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  qpat_x_assum `!DF lo d PG tops ctx sc f sf cenv env ty es.
    _ ==> expr_sim_full _ cenv cx ty e es /\ _` (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`, `shadow_ctx`,
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
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  qpat_assum `body_inv tops ctx cenv cx`
    (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules
      o MATCH_MP body_inv_contract) >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`,
                     `s` |-> `Expr e`]
             stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supported_stmt_expr_exists_def, int_calls_stmt_def] >>
     disch_then irule >>
     `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def] >>
     `~is_extcode e` by metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode] >>
     mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `calls` |-> `[]`]
              stmt_expr_body_pre_main_mods) >>
     gvs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
         stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def]) >>
  irule compile_expr_stmt_frag_ok_full >>
  simp[gas_shadow_stmt_compile_expr] >> conj_tac
  >- (rpt strip_tac >>
      `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
      drule_all compile_expr_open_general >> simp[]) >>
  qpat_x_assum `body_expr_full_ok _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  qpat_x_assum `!DF lo d PG tops ctx sc f sf cenv env ty es.
    _ ==> expr_sim_full _ cenv cx ty e es /\ _` (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`, `shadow_ctx`,
    `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`] mp_tac) >>
  simp[]
QED

(* ===== If ===== *)

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
  qpat_assum `body_inv tops ctx cenv cx`
    (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules
      o MATCH_MP body_inv_contract) >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`,
                     `s` |-> `If e ss1 ss2`]
              stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supported_stmt_expr_exists_def] >>
     disch_then irule >>
     `supported_expr tops e /\ well_typed_expr env e` by
       fs[supported_stmt_def, supported_expr_def, type_stmt_def, optionTheory.IS_SOME_EXISTS] >>
     `alloc_limits_expr cenv e` by
       fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def] >>
     drule_then assume_tac allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
     drule_then assume_tac (cj 1 allocLimitsPropsTheory.alloc_limits_expr_exists) >>
     mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                      `calls` |-> `int_calls_stmts ss1 ++ int_calls_stmts ss2`]
              stmt_expr_body_pre_main_mods) >>
     gvs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
         stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def,
         DE_MORGAN_THM, LEFT_AND_OVER_OR, supported_expr_exists_disj]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
      supported_stmt_expr_exists_def, DE_MORGAN_THM]) >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  `expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cenv cx (BaseT BoolT) e es` by
    (qpat_x_assum `body_expr_full_ok _ _`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     qpat_x_assum `!DF lo d PG tops ctx sc f sf cenv env ty es.
       _ ==> expr_sim_full _ cenv cx ty e es /\ _` (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
       `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `BaseT BoolT`,
       `es`] mp_tac) >> simp[]) >>
  `ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
    !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (strip_tac >> qpat_assum `body_inv _ ctx _ cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP body_inv_no_phi (CONJ inv member))))) >>
  irule compile_if_stmt_frag_full >>
  simp[stmts_env_cs_mono] >> rpt conj_tac
  >~ [`gas_shadow_compiles _ _`]
  >- irule gas_shadow_stmt_lower_value_env
  >~ [`gas_shadow_compiles_env _ _ (stmts_env _ _ _ (MAP gas_shadow_stmt ss1))`]
  >- irule gas_shadow_stmts_env_env
  >~ [`gas_shadow_compiles_env _ _ _`]
  >- irule gas_shadow_stmts_env_env
  >- (rpt gen_tac >> disch_tac >> drule (CONJUNCT2 compile_expr_grows) >> simp[])
  >- (rpt gen_tac >> disch_tac >> drule (CONJUNCT2 compile_expr_grows) >> simp[]) >>
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
  `body_const_cells_agree [(NONE,tops)] cx env es1` by
    (irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env
      (es1 with scopes updated_by CONS FEMPTY)` by
    (irule (iffLR body_const_cells_agree_immutables) >>
     qexists_tac `es1` >> simp[]) >>
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
  `ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
    !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (strip_tac >> qpat_assum `body_inv _ ctx _ cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP body_inv_no_phi (CONJ inv member))))) >>
  irule (REWRITE_RULE [MAP] stmt_frag_full_cons_env) >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `body_stmt_full_ok _ _`
        (irule o REWRITE_RULE [body_stmt_full_ok_def]) >>
      metis_tac[call_evaluation_safe_append_left]) >>
  rpt strip_tac >>
  rename1 `stmt_env cenv lctx ret_ty s sa = (c, sm)` >>
  `same_frame cenv c` by metis_tac[cenv_top_ext_same_frame] >>
  `stmts_exprs_ok c = stmts_exprs_ok (decl_var_type cenv s)` by
    metis_tac[stmt_env_stmts_exprs_ok] >>
  `expr_sim_inv c cx env1 es1` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (strip_assume_tac o MATCH_MP body_inv_main_support) >>
     qpat_assum `body_inv tops ctx cenv cx`
       (assume_tac o MATCH_MP contract_inv_alloca_locals o MATCH_MP body_inv_contract) >>
     irule expr_sim_inv_stmt >> simp[] >>
     metis_tac[expr_sim_inv_gas_obs, call_evaluation_safe_append_left]) >>
  `body_const_cells_agree [(NONE,tops)] cx env1 es1` by
    (irule body_const_cells_agree_stmt >>
     goal_assum (drule_at (Pat `eval_stmt _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >> simp[]) >>
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
