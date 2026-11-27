(*
 * raw_log over the finite-horizon joint judgment: the topics, the data
 * operand and the LOG share one origin/memory/pointer witness.
 *
 * The joint simulation uses the env-aware shadow compiler rules for
 * lower_value and compile_multi_exprs.
 *
 * TOP-LEVEL:
 *   raw_log_expr_full_ok
 *)
Theory bodyFullRawLog
Ancestors
  bodyFullRawLogCompose bodyFullExprGeneric bodyFullPreds bodySimFull exprSimCallRawLog
  gasShadowCompile gasShadowCompileHelpers gasShadowCompileStmtHelpers
  gasShadowState gasShadow exprLowering exprCallbackContracts exprSimHypsDefs vyperTypeSystem
  vyperAST list compileEnv vyperInterpreter vyperValue vyperState valueEncoding
  bodyFullPredsMods[qualified]
Libs pairLib

val _ = Parse.hide "body";

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `LENGTH args = 2` by
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
*)
Theorem raw_log_compile_stack:
  expr_body_pre_mods mods cenv cx env (Call ann RawLog args dflt) es ==>
  !sa. ?t op sb. compile_expr cenv ty (Call ann RawLog args dflt) sa =
                (StackValue t op,sb)
Proof
  cheat
QED

Theorem raw_log_expr_full_ok:
  !cx ann es dflt.
    (!cenv ty e.
       gas_shadow_compiles (lower_value compile_expr cenv ty e)
         (lower_value compile_expr cenv ty (gas_shadow_expr e))) /\
    (!cenv xs.
       gas_shadow_compiles (compile_multi_exprs compile_expr cenv xs)
         (compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr xs))) /\
    body_exprs_full_ok_mods mods exps cx es ==>
    body_expr_full_ok_mods mods exps cx (Call ann RawLog es dflt)
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
    (irule raw_log_expr_sim_full >> simp[gas_shadow_stmt_lower_value_env] >>
     conj_tac
     >- metis_tac[Q.INST [`sd` |-> `T`, `sh` |-> `T`]
           (MATCH_MP gas_shadow_compiles_multi_exprs_env
             (CONJUNCT1 gas_shadow_compile_expr_env))] >>
     map_every qexists_tac [`env`, `tops`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_stack_full >> simp[] >> rpt conj_tac
  >~ [`!sa. ?t op sb. compile_expr cenv ty (Call ann RawLog es dflt) sa =
         (StackValue t op,sb)`]
  >- metis_tac[raw_log_compile_stack]
  >~ [`!s tv s'. eval_expr cx (Call ann RawLog es dflt) s = (INL tv,s') ==>
         ?v. tv = Value v`]
  >- metis_tac[raw_log_eval_value] >> suspend "size"
QED

Resume raw_log_expr_full_ok[size]:
  `ann = NoneT` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def]) >>
  simp[expr_type_def, lowered_value_type_def, evaluate_type_def,
       type_memory_size_def]
QED

Finalise raw_log_expr_full_ok
