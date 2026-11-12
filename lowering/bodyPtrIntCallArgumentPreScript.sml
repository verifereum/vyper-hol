(* Source-side prerequisites for internal-call argument evaluation. *)
Theory bodyPtrIntCallArgumentPre
Ancestors
  bodyExprPreFacts bodyPtrIntCallStageArgument exprSimHyps
  supportedExprs supportedExprTraverse exprSimHypsDefs
  vyperInterpreter vyperState list exprSimSource vyperTypeSystem
  bodyIntCallSource entryArgPtrs entryDecodeProps compileEnv

Theorem intcall_supported_operands:
  supported_expr tops (Call ann (IntCall name) args dflt) ==>
  supported_pure_exprs tops args
Proof
  Cases_on `dflt` >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem intcall_operand_post_value_types:
  supported_expr tops (Call ann (IntCall name) args dflt) ==>
  EVERY (\e. post_value_type ce e = expr_type e) args
Proof
  strip_tac >> drule intcall_supported_operands >>
  simp[supported_pure_exprs_every, EVERY_MEM] >> rpt strip_tac >>
  irule post_value_type_no_calls >> metis_tac[supported_pure_int_calls]
QED

Theorem expr_body_pre_intcall_arg:
  !ce cx env ann name args dflt e es ee.
    expr_body_pre ce cx env (Call ann (IntCall name) args dflt) es /\
    MEM e args /\ expr_sim_inv ce cx env ee ==>
    expr_body_pre ce cx env e ee
Proof
  rpt gen_tac >> PairCases_on `name` >>
  rw[expr_body_pre_def, well_typed_expr_def,
     vyperTypeCallGraphTheory.int_calls_expr_def,
     byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, EXISTS_MEM]
  >- metis_tac[well_typed_exprs_member]
  >- metis_tac[byte_widths_exprs_mem]
  >- metis_tac[alloc_limits_exprs_mem]
  >- (irule call_evaluation_safe_exprs_mem >> qexists_tac `args` >>
      simp[] >> irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
      goal_assum (drule_at Any) >> simp[])
  >> metis_tac[]
QED

(* The source invariant is carried through the actual evaluation prefix. *)
Theorem body_pre_results_source:
  !args ce cx env es res ee.
    (!e s. MEM e args /\ expr_sim_inv ce cx env s ==>
       expr_body_pre ce cx env e s) /\
    expr_sim_inv ce cx env es /\
    eval_expr_results cx args es = (res,ee) ==>
    expr_sim_inv ce cx env ee /\
    (case res of INL raws => LENGTH raws = LENGTH args
     | INR exc => expr_vv_res_ok (INR exc))
Proof
  Induct_on `args`
  >- simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre ce cx env h es` by metis_tac[MEM] >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >>
  imp_res_tac exprSimSourceTheory.expr_body_pre_eval_result >>
  imp_res_tac expr_body_pre_vv_res_ok >>
  gvs[] >>
  `!e s. MEM e args /\ expr_sim_inv ce cx env s ==>
     expr_body_pre ce cx env e s` by metis_tac[] >>
  first_x_assum (qspecl_then [`ce`,`cx`,`env`,`s''`] mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem intcall_operand_gas_admissible:
  expr_body_pre ce cx env (Call ann (IntCall name) args dflt) es /\
  MEM e args /\ expr_sim_inv ce cx env ee ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok ee
Proof
  metis_tac[expr_body_pre_intcall_arg, expr_body_pre_vv_gas_admissible]
QED

Theorem intcall_results_gas_admissible:
  expr_body_pre ce cx env (Call ann (IntCall name) args dflt) es ==>
  gas_admissible (eval_expr_results cx args)
    (\res. case res of INL raws => LENGTH raws = LENGTH args
           | INR exc => expr_vv_res_ok (INR exc)) es
Proof
  strip_tac >> rw[gasContextTheory.gas_admissible_def] >>
  drule_at (Pos last) body_pre_results_source >>
  disch_then (qspecl_then [`ce`,`env`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- metis_tac[expr_body_pre_intcall_arg] >>
      metis_tac[expr_body_pre_gas_obs, expr_body_pre_def]) >>
  simp[]
QED

Theorem intcall_operand_declared_type:
  expr_body_pre ce cx env (Call ann (IntCall (src,name)) es dflt) st /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy name ts =
    SOME (mut,nr,params,dflts,ret,ss) /\ i < LENGTH es ==>
  i < LENGTH params /\ expr_type (EL i es) = SND (EL i params)
Proof
  strip_tac >>
  `well_typed_expr env (Call ann (IntCall (src,name)) es dflt) /\
   fn_sigs_consistent env.fn_sigs cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all typed_intcall_source_signature >> strip_tac >> gvs[] >>
  rename1 `MAP expr_type es = TAKE (LENGTH es) (MAP SND ps)` >>
  `EL i (MAP expr_type es) =
   EL i (TAKE (LENGTH es) (MAP SND ps))` by metis_tac[] >>
  gvs[EL_MAP, EL_TAKE]
QED

Theorem compute_pass_via_stack_words:
  !tys n i. i < LENGTH tys /\ EL i (compute_pass_via_stack tys n) ==>
    is_word_type (EL i tys)
Proof
  Induct_on `tys` >> simp[compute_pass_via_stack_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  Cases_on `i` >> simp[] >> metis_tac[]
QED

Theorem intcall_staging_value_types:
  expr_body_pre ce cx env (Call ann (IntCall (src,name)) es dflt) st /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy name ts =
    SOME (mut,nr,params,dflts,ret,ss) /\
  bind_arguments (get_tenv cx) params vs = SOME penv /\ i < LENGTH es ==>
  arg_type_fits (expr_type (EL i es)) (SND (EL i params)) /\
  ?stv dtv.
    evaluate_type (get_tenv cx) (expr_type (EL i es)) = SOME stv /\
    evaluate_type (get_tenv cx) (SND (EL i params)) = SOME dtv /\
    val_wf stv (EL i vs) /\ val_wf dtv (EL i vs)
Proof
  strip_tac >> drule_all intcall_operand_declared_type >> strip_tac >>
  simp[] >> conj_tac
  >- (qsuff_tac `!ty. arg_type_fits ty ty` >- simp[] >>
      Induct >> simp[vyperTypeSystemTheory.arg_type_fits_def]
      >- (Cases >> simp[vyperTypeSystemTheory.arg_type_fits_def] >>
          rename1 `BytesT bd` >> Cases_on `bd` >>
          simp[vyperTypeSystemTheory.arg_type_fits_def])
      >- (Induct_on `l` >> simp[vyperTypeSystemTheory.arg_type_fits_def]) >>
      Cases >> simp[vyperTypeSystemTheory.arg_type_fits_def]) >>
  drule_all bind_arguments_word_arg >> strip_tac >>
  drule_all bind_arguments_memory_wf >> metis_tac[]
QED
