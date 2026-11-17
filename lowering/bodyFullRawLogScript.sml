(*
 * raw_log over the finite-horizon joint judgment: the topics, the data
 * operand and the LOG share one origin/memory/pointer witness.
 *
 * The two shadow-compile premises are the lower_value and
 * compile_multi_exprs forms of the gas-shadow compile spine
 * (gas_shadow_compiles_lower_value with gas_shadow_compile_expr, and
 * gas_shadow_compiles_multi_exprs), which this base doesn't carry yet;
 * body_raw_log_case_full discharges them once it does.
 *
 * TOP-LEVEL:
 *   raw_log_expr_full_ok
 *)
Theory bodyFullRawLog
Ancestors
  bodyFullRawLogCompose bodyFullExprGeneric bodyFullPreds bodySimFull
  gasShadowState gasShadow exprLowering exprCallbackContracts exprSimHypsDefs vyperTypeSystem
  vyperAST list compileEnv vyperInterpreter vyperValue vyperState valueEncoding
Libs pairLib

val _ = Parse.hide "body";

Theorem raw_log_expr_full_ok:
  !cx ann es dflt.
    (!cenv ty e.
       gas_shadow_compiles (lower_value compile_expr cenv ty e)
         (lower_value compile_expr cenv ty (gas_shadow_expr e))) /\
    (!cenv xs.
       gas_shadow_compiles (compile_multi_exprs compile_expr cenv xs)
         (compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr xs))) /\
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ann RawLog es dflt)
Proof
  rpt gen_tac >> strip_tac >>
  pure_once_rewrite_tac [body_expr_full_ok_def] >> conj_tac
  >- suspend "judgments" >> simp[]
QED

Resume raw_log_expr_full_ok[judgments]:
  qx_genl_tac [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,
    `shadow_func`,`cenv`,`env`,`ty`,`start`] >> strip_tac >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Call ann RawLog es dflt) start` by
    (irule raw_log_expr_sim_full >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- (qexists_tac `tops` >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_stack_full >> simp[] >> rpt conj_tac
  >~ [`!sa. ?t op sb. compile_expr cenv ty (Call ann RawLog es dflt) sa =
         (StackValue t op,sb)`]
  >- suspend "stack"
  >~ [`!s tv s'. eval_expr cx (Call ann RawLog es dflt) s = (INL tv,s') ==>
         ?v. tv = Value v`]
  >- suspend "value" >> suspend "size"
QED

Resume raw_log_expr_full_ok[size]:
  `ann = NoneT` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def]) >>
  simp[expr_type_def, lowered_value_type_def, evaluate_type_def,
       type_memory_size_def]
QED

Resume raw_log_expr_full_ok[stack]:
  `LENGTH es = 2` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def]) >>
  gvs[LENGTH_EQ_NUM_compute] >> gen_tac >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def] >>
  pure_rewrite_tac [compile_expr_body_def, expr_type_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[compile_call_child_calls, compile_call_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> simp[])
QED

Resume raw_log_expr_full_ok[value]:
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       type_check_def, assert_def, raise_def, lift_option_type_def,
       lift_option_def, push_log_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Finalise raw_log_expr_full_ok
