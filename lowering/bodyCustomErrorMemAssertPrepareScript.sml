Theory bodyCustomErrorMemAssertPrepare
Ancestors
  bodySim bodyMemoryPreds vyperState gasContext bodyCustomErrorSource bodyExprPreFacts exprSimSource supportedExprs
  supportedStmtTraverse loweringPosts vyperInterpreter vyperAST
  vyperTypeCallGraph vyperTypeSystem vyperTypeContract

Theorem body_assert_custom_error_mem_prepare:
  ((!cx err d tops ctx func cenv env env' ret_ty lctx RetQ es.
    body_inv tops ctx cenv cx /\
    EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
    custom_error_resolved [(NONE,tops)] err /\
    (!target. supported_stmt_expr_exists
      (expr_abi_decode_target_root target) (Raise (RaiseCustomError err)) ==>
      occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    body_exprs_mem_ok cx (custom_error_exprs err) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
      (eval_stmt cx (Raise (RaiseCustomError err))) es) /\
   (!d ctx func cx lctx RetQ cenv ty e err es.
    expr_type e = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1.
       (do raw <- eval_expr cx e; read_result cx raw od)
         (es with gas_obs := gs) = (INL (BoolV F),es1) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ty (Raise (RaiseCustomError err)))
         (eval_stmt cx (Raise (RaiseCustomError err))) es1) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertCustomError err)))
      (eval_stmt cx (Assert e (AssertCustomError err))) es)) ==>
  (!cx e err.
     body_expr_mem_ok cx e /\
     (!s0 tv s1 id positional kwargs decls params args.
        eval_expr cx e s0 = (INL tv,s1) /\
        err = CustomError id positional kwargs /\
        get_module_code cx (FST id) = SOME decls /\
        lookup_custom_error_args_in (SND id) decls = SOME params /\
        order_custom_error_args params err = SOME args ==>
        body_exprs_mem_ok cx args) ==>
     !d tops ctx func cenv env env' ret_ty lctx RetQ es.
       body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
       EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
       custom_error_resolved [(NONE,tops)] err /\
       (!target. supported_stmt_expr_exists
          (expr_abi_decode_target_root target) (Assert e (AssertCustomError err)) ==>
          occurs_abi_decode_target target tops) /\
       expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
       locals_alloc_ok cenv env /\
       type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
       stmt_exprs_ok cenv (Assert e (AssertCustomError err)) /\
       call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) /\
       frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ret_ty (Assert e (AssertCustomError err)))
         (eval_stmt cx (Assert e (AssertCustomError err))) es)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `expr_type e = BaseT BoolT /\ well_typed_expr env e` by
    gvs[type_stmt_def] >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `expr_body_pre cenv cx env e es` by
    (`cx_tops cx = tops` by
       (irule cx_tops_module >> fs[body_inv_def]) >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     conj_tac >- fs[body_inv_def] >>
     qexists_tac `int_calls_assert_reason (AssertCustomError err)` >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (BaseT BoolT) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  qpat_x_assum `!d ctx func cx lctx RetQ cenv ty e err es. _` irule >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env e (es with gas_obs := gs)` by
    metis_tac[expr_sim_pre_body, expr_sim_pre_gas_obs] >>
  drule_all expr_sim_pre_eval >> strip_tac >>
  `?tv t. eval_expr cx e (es with gas_obs := gs) = (INL tv,t)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_exprs_mem_ok cx (custom_error_exprs err)` by
    (Cases_on `err` >> drule_all custom_error_body_resolution >>
     strip_tac >> metis_tac[]) >>
  qpat_x_assum `!cx err d tops ctx func cenv env env' ret_ty lctx RetQ es. _` irule >>
  simp[] >> rpt conj_tac
  >~ [`call_evaluation_safe _ _`]
  >- gvs[int_calls_stmt_def, int_calls_assert_reason_def, int_calls_raise_reason_def]
  >~ [`stmt_exprs_ok _ _`]
  >- gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assert_exists_def, supported_raise_exists_def,
         allocLimitsTheory.alloc_limits_stmt_def, allocLimitsTheory.alloc_limits_raise_def,
         allocLimitsTheory.alloc_limits_assert_def,
         compileVyperTheory.stmt_valued_return_def]
  >- (qexists_tac `tops` >> gvs[supported_stmt_expr_exists_def,
        supported_assert_exists_def, supported_raise_exists_def] >> metis_tac[]) >>
  qexistsl_tac [`env`,`env'`] >> gvs[type_stmt_def]
QED
