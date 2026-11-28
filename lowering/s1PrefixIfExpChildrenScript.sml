(* Request-prefix composition for an ordinary conditional expression. *)
Theory s1PrefixIfExpChildren
Ancestors
  s1PrefixIfExpPrepare bodyFullSimProjection s1PrefixOfVV s1PrefixPreds
  bodyFullIfExpPrepare bodyFullPreds immutableDeployAssignRanges
  exprBodyPreProps exprSimHyps exprSimSource exprSimIfExp exprSimDefs
  vyperAST vyperInterpreter vyperState vyperTypeSystem

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule bodyFullIfExpPrepareTheory.ifexp_body_pre_children >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env e1` by
    metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts] >>
  drule_all immutable_assign_copy_metadata >> strip_tac >>
  `?rty. evaluate_type (get_tenv cx) v5 = SOME rty` by
    (qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _`
       (mp_then Any mp_tac exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) e1 es` by
    (drule_all bodyFullSimProjectionTheory.body_expr_full_ok_simulations >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) e1 es` by
    (qpat_assum `body_expr_prefix_ok cx e1`
       (mp_then Any mp_tac (iffLR (CONJUNCT1 body_expr_prefix_ok_def))) >>
     strip_tac >> first_x_assum (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,
       `ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`BaseT BoolT`,`es`] mp_tac) >>
     simp[]) >>
  `!t tv. evaluate_type (get_tenv cx) t = SOME tv ==>
     type_memory_bytes cenv t = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `!tv. evaluate_type (get_tenv cx) v5 = SOME tv /\ ~is_word_type v5 ==>
     type_memory_size tv < 2 ** 64` by
    (qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _`
       (mp_then Any mp_tac exprSimHypsTheory.expr_body_pre_copy_ok) >>
     simp[expr_type_def]) >>
  `!gs v es1. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gs) = (INL v,es1) ==>
    body_const_cells_agree [(NONE,tops)] cx env es1 /\
    expr_body_pre cenv cx env e2 es1 /\ expr_body_pre cenv cx env e3 es1 /\
    body_expr_full_ok cx e2 /\ body_expr_full_ok cx e3 /\
    body_expr_prefix_ok cx e2 /\ body_expr_prefix_ok cx e3` by
    (rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by
       simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
     `expr_sim_inv cenv cx env es1` by
       (qpat_assum `expr_body_pre _ _ _ e1 (_ with gas_obs := _)`
          (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_eval) >>
        simp[] >> metis_tac[]) >>
     conj_tac
     >- (irule bodyFullPredsTheory.body_const_cells_agree_expr_read >>
         qpat_assum `bind (eval_expr cx e1) _ _ = (_,es1)` (irule_at Any) >>
         simp[]) >>
     qpat_assum `!es'. expr_sim_inv cenv cx env es' ==> _` drule >> strip_tac >>
     qpat_x_assum `bind (eval_expr cx e1) _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  irule ifexp_vv_prefix_root_uniform >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "arm_prefix" >>
  qexistsl [`env`,`rty`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "arm_step" >>
  suspend "arm_full"
QED
*)
Theorem ifexp_prefix_from_child_cases:
  !cx v5 e1 e2 e3.
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_prefix_ok cx e2) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_prefix_ok cx e3) /\
  body_expr_full_ok cx e1 /\
  body_expr_prefix_ok cx e1 ==>
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (IfExp v5 e1 e2 e3) es ==>
    expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (IfExp v5 e1 e2 e3) es /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (IfExp v5 e1 e2 e3) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume ifexp_prefix_from_child_cases[arm_prefix]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!gs v es1. bind _ _ _ = _ ==> _` drule >> strip_tac >>
  conj_tac
  >- (qpat_assum `body_expr_prefix_ok cx e2`
        (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
      disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
        `func`,`shadow_func`,`cenv`,`env`,`ty`,`es1`] mp_tac) >> simp[]) >>
  qpat_assum `body_expr_prefix_ok cx e3`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
    `func`,`shadow_func`,`cenv`,`env`,`ty`,`es1`] mp_tac) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ifexp_prefix_from_child_cases[arm_step]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type e = v5 /\ expr_body_pre cenv cx env e es` by metis_tac[] >>
  qpat_assum `expr_body_pre _ _ _ e es`
    (mp_then Any (map_every assume_tac o CONJUNCTS)
      bodyFullIfExpPrepareTheory.ifexp_body_arm_kind) >>
  irule bodyFullIfExpPrepareTheory.ifexp_selected_arm_step_full >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`e`,`env`,`rty`,`sm`,`ty`,`av`] >> simp[] >>
  Cases_on `same_memory_layout cenv (lowered_value_type cenv e) v5` >>
  Cases_on `post_value_type cenv e = v5` >> gvs[] >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ifexp_prefix_from_child_cases[arm_full]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!gs v es1. bind _ _ _ = _ ==> _` drule >> strip_tac >>
  ntac 2 (conj_tac >-
    (irule (bodyFullSimProjectionTheory.body_expr_full_ok_simulations |> UNDISCH |> CONJUNCT2 |> DISCH_ALL) >>
     metis_tac[])) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env e (es1 with gas_obs := gs')` by
        metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs] >>
      drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type e = v5 /\ expr_body_pre cenv cx env e (es1 with gas_obs := gs')` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  conj_tac
  >- (qpat_assum `expr_body_pre _ _ _ e (_ with gas_obs := _)`
        (mp_then Any mp_tac exprSimIfExpTheory.ifexp_body_pre_read_typed) >>
      simp[] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    metis_tac[exprBodyPrePropsTheory.expr_body_pre_env_type_defs] >>
  qpat_assum `expr_body_pre _ _ _ e (_ with gas_obs := _)`
    (mp_then Any mp_tac exprSimHypsTheory.memory_rhs_read_post_typed) >>
  disch_then (qspecl_then [`v'`,`es2`] mp_tac) >>
  gvs[SF ETA_ss, vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  strip_tac >> rpt strip_tac >> gvs[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise ifexp_prefix_from_child_cases
*)
