(* Memory case of the body induction (bodyMemory's body_mem_mutual): assert
   with a reason string.  A string literal goes to
   stmtReasonLitAssertMemory; any other reason through its value_vv
   (stmtReasonVvMemory) to the revert path of its kind
   (stmtReasonKindsMemory), where the condition is false. *)
Theory bodyMemAssertReason
Ancestors
  allocLimitsProps
  bodyMemoryPreds stmtReasonLitAssertMemory stmtReasonVvMemory
  stmtReasonKindsMemory bodyExprPreFacts exprSimSource exprLoweringProps
  bodySim supportedStmtTraverse supportedExprTraverse supportedStmts
  supportedExprs vyperTypeSystem exprSimHyps allocLimits gasContext
  vyperAST vyperTypeCallGraph compileEnv exprSimHypsDefs vyperState

(* The reason simulates where the condition is false: both are pure, so
   the condition's evaluation keeps expr_sim_inv (expr_sim_pre_eval). *)
Theorem assert_reason_vv_sim_mem[local]:
  !cx e se tops ctx func cenv env es gs es1.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_mem_ok cx se) /\
    body_inv tops ctx cenv cx /\ expr_sim_pre cenv cx env e es /\
    well_typed_expr env se /\ int_calls_expr se = [] /\
    ~expr_has_evm_run se /\ ~is_extcode se /\
    ~supported_expr_exists call_operands_effect_root se /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) se /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) se ==>
              occurs_abi_decode_target target (cx_tops cx)) /\
    (do raw <- eval_expr cx e; read_result cx raw od)
      (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
    expr_vv_sim_mem ctx func cenv cx (expr_type se) se es1
Proof
  rpt strip_tac >>
  `expr_sim_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all expr_sim_pre_eval >> strip_tac >>
  `?tv t. eval_expr cx e (es with gas_obs := gs) = (INL tv, t)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_expr_mem_ok cx se` by metis_tac[] >>
  `byte_widths_expr se /\ alloc_limits_expr cenv se` by
    (CCONTR_TAC >>
     qpat_x_assum `~supported_expr_exists (\e. ~is_extcode e /\ _) _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  `expr_body_pre cenv cx env se es1` by
    gvs[expr_body_pre_def, expr_sim_pre_def] >>
  metis_tac[body_expr_mem_ok_def]
QED

Theorem body_assert_reason_mem_case:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_mem_ok cx se) /\
    body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (Assert e (AssertReason se))
Proof
  rw[body_stmt_mem_ok_def] >>
  `supported_pure_expr tops e /\ supported_string_reason tops se` by
    gvs[supported_stmt_def, supported_assert_reason_def] >>
  `expr_type e = BaseT BoolT /\ well_typed_expr env e /\
   well_typed_expr env se` by gvs[type_stmt_def] >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `~expr_has_evm_run se /\ ~is_extcode se /\
   ~supported_expr_exists call_operands_effect_root se` by
    simp[] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def, body_inv_def] >>
     qexists_tac `int_calls_assert_reason (AssertReason se)` >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (BaseT BoolT) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  `!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
              cs_extends sa sb` by metis_tac[compile_expr_grows] >>
  `~supported_expr_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) se` by
    gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
        supported_assert_exists_def] >>
  `alloc_limits_expr cenv se` by
    (CCONTR_TAC >> qpat_x_assum `~supported_expr_exists _ se` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> fs[]) >>
  `!target. supported_expr_exists (expr_abi_decode_target_root target) se ==>
            occurs_abi_decode_target target (cx_tops cx)` by
    (fs[supported_stmt_expr_exists_def,
        supported_assert_exists_def] >> metis_tac[]) >>
  Cases_on `?ml str. se = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_assert_reason_lit_frag_mem >>
      gvs[well_typed_expr_def, well_typed_literal_def] >>
      drule alloc_limits_expr_type_alloc_ok >>
      simp[type_alloc_ok_def, expr_type_def, is_word_type_def]) >>
  `int_calls_expr se = []` by
    (Cases_on `?t str. se = Literal t (StringL str)`
     >- gvs[int_calls_expr_def] >>
     `supported_pure_expr tops se` suffices_by
       metis_tac[supported_pure_int_calls] >>
     Cases_on `se` >> gvs[supported_string_reason_def] >>
     rename1 `Literal _ lit` >> Cases_on `lit` >>
     gvs[supported_string_reason_def]) >>
  `!gs es1. (do raw <- eval_expr cx e; read_result cx raw od)
              (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
            expr_vv_sim_mem ctx func cenv cx (expr_type se) se es1` by
    (rpt strip_tac >> irule assert_reason_vv_sim_mem >>
     simp[expr_sim_pre_body] >> metis_tac[]) >>
  irule compile_assert_reason_vv_frag_mem >> fs[] >>
  rpt strip_tac >> metis_tac[reason_revert_path_mem]
QED
