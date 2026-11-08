(* Independent source and typing boundaries for RawLog body simulation. *)
Theory bodySimRawLogBodySource
Ancestors
  bodySim bodySimExprCases exprSimSend exprSimHyps vyperTypeSystem vyperAST list
  exprSimAggregateSource vyperInterpreter vyperValue vyperState vyperContext
  exprSimWordArgs exprLowering compileEnv emitHelper venomExecSemantics
  exprLoweringProps venomState venomMemDefs exprSimDefs exprSimStack loweringPosts exprSimHypsDefs exprSimSource vyperEvent fragExec venomInst
  exprSimHash exprSimBuffer exprSimPrecompiles emitHelperProps ASCIInumbers exprSimRawLog
  bodySimRawLogSource
Libs
  pairLib

Theorem raw_log_body_data_after_topics:
  body_exprs_ok cx [topics; data] /\
  eval_expr cx topics s = (INL tv, t) /\
  read_result cx tv s1 = (INL v, t1) ==>
  body_expr_ok cx data
Proof
  simp[body_exprs_ok_def] >> metis_tac[]
QED

Theorem raw_log_body_pre_shape:
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es ==>
  ?a elem bd topics data n.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    ann = NoneT /\ dflt = NONE /\ LENGTH topics <= 4 /\
    a = ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n) /\ n <= 4 /\
    well_typed_expr env (Builtin a (MakeArray elem bd) topics) /\
    well_typed_expr env data /\
    (expr_type data = BaseT (BytesT (Fixed 32)) \/
     ?m. expr_type data = BaseT (BytesT (Dynamic m)))
Proof
  simp[expr_body_pre_def, Once well_typed_expr_def] >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute] >>
  Cases_on `h` >> gvs[] >>
  rename1 `Builtin a b topics` >> Cases_on `b` >>
  gvs[expr_type_def, well_typed_expr_def] >> metis_tac[]
QED

Theorem raw_log_literal_typed:
  well_typed_expr env
    (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
      (MakeArray elem bd) topics) ==>
  elem = SOME (BaseT (BytesT (Fixed 32))) /\ bd = Dynamic n /\
  LENGTH topics <= n /\
  EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
  builtin_args_length_ok (MakeArray elem bd) (LENGTH topics)
Proof
  Cases_on `elem` >>
  simp[well_typed_expr_def, well_typed_builtin_app_def,
       vyperValueTheory.compatible_bound_def,
       vyperContextTheory.builtin_args_length_ok_def] >>
  rpt strip_tac >> gvs[vyperValueTheory.compatible_bound_def]
QED

Theorem expr_body_pre_raw_log_arg:
  !cenv cx env ann args dflt e es es'.
    expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def,
     vyperTypeCallGraphTheory.int_calls_expr_def,
     byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Theorem raw_log_body_topics_ready:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx topics /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) ==>
  typed_args_ready ctx func cenv cx expr_type
    (\s. expr_sim_inv cenv cx env s) topics
Proof
  strip_tac >> simp[SF ETA_ss] >> irule typed_args_ready_of_case >>
  qexists_tac `F` >> simp[] >> conj_tac
  >- (rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  metis_tac[body_exprs_ok_case]
QED

Theorem raw_log_body_topics_success:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx topics /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  eval_exprs cx topics es = (INL vs,es') ==>
  expr_sim_inv cenv cx env es'
Proof
  strip_tac >> drule_all raw_log_body_topics_ready >>
  disch_then (qspec_then `func` assume_tac) >>
  drule typed_args_ready_success >> simp[] >>
  disch_then (qspec_then `es` mp_tac) >> simp[] >>
  disch_then drule >> simp[]
QED

Theorem raw_log_body_topics_values:
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  eval_exprs cx topics es = (INL vs,es') ==>
  EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
  EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs
Proof
  strip_tac >>
  `EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics)` by
    (simp[EVERY_MAP, EVERY_MEM] >> metis_tac[]) >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) topics vs` by
    (irule stack_args_values_typed_body >> goal_assum (drule_at Any) >>
     qexistsl_tac [`cenv`, `env`] >> simp[] >>
     rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  simp[] >> fs[EVERY_MAP, EVERY_EL, LIST_REL_EL_EQN] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[vyperValueTheory.evaluate_type_def] >> metis_tac[]
QED

Theorem raw_log_body_compile_stack:
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es ==>
  !sa. ?sb. compile_expr cenv ty (Call ann RawLog args dflt) sa =
    (StackValue ann (Lit 0w),sb)
Proof
  strip_tac >> drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  gen_tac >> simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  Cases_on `expr_type data = BaseT (BytesT (Fixed 32))` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem raw_log_body_eval_value:
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es ==>
  !tv es'. eval_expr cx (Call ann RawLog args dflt) es = (INL tv,es') ==>
    ?v. tv = Value v
Proof
  strip_tac >> drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  (Cases_on `cx.txn.is_static`
  >- (simp[Once evaluate_def] >>
      simp[bind_def, ignore_bind_def, check_not_static_def, assert_def,
           raise_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[]) >>
  simp[raw_log_source_eval, bind_def, lift_option_type_def, type_check_def,
       assert_def, push_log_def, ignore_bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[])
QED

Theorem raw_log_body_lower_value:
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  lower_value compile_expr cenv ty (Call ann RawLog args dflt) sa = (op,sb) ==>
  op = Lit 0w /\
  compile_expr cenv ty (Call ann RawLog args dflt) sa = (StackValue ann (Lit 0w),sb)
Proof
  strip_tac >> drule raw_log_body_compile_stack >>
  disch_then (qspecl_then [`ty`, `sa`] strip_assume_tac) >>
  gvs[lower_value_def, unwrap_value_def, comp_bind_def, comp_return_def]
QED
