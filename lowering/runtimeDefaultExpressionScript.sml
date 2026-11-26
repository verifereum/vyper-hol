(* Runtime-constant syntax avoids the internal-call induction. *)
Theory runtimeDefaultExpression
Ancestors
  bodyFullCases bodyFullPreds bodyFullSimProjection whitelistCheckerConsts vyperTypeContract
  exprCallBounds exprLowering exprSimSource exprSimFullBundleProps
  gasOutcomeFullCompose abiEncodeArgsScopes vyperScopePreservation
  bodySimFull targetPureSourceFrame supportedExprTraverse
  vyperInterpreter vyperState vyperAST vyperContext arithmetic list pair

Theorem every_body_expr_full_ok[local]:
  EVERY (body_expr_full_ok cx) es ==> body_exprs_full_ok cx es
Proof
  Induct_on `es` >> simp[body_exprs_full_ok_def]
QED

Theorem runtime_constant_expr_body_full_ok:
  runtime_constant_expr mods e ==> body_expr_full_ok cx e
Proof
  completeInduct_on `expr_size e` >> Cases_on `e` >> rpt strip_tac >>
  gvs[PULL_FORALL, runtime_constant_expr_def, EVERY_MEM] >>
  TRY (irule body_expr_full_ok_leaf >> simp[] >> NO_TAC) >>
  TRY (irule body_ifexp_case_full >> rpt strip_tac >>
       first_x_assum irule >> simp[] >> NO_TAC)
  >~ [`body_expr_full_ok _ (Subscript _ _ _)`]
  >- (irule body_subscript_case_full >> rpt strip_tac >>
      first_x_assum irule >> simp[])
  >~ [`body_expr_full_ok _ (Attribute _ _ _)`]
  >- (irule body_attribute_case_full >> rpt strip_tac >>
      first_x_assum irule >> simp[])
  >~ [`body_expr_full_ok _ (StructLit _ _ _)`]
  >- (rename1 `StructLit ann nsid fs` >> PairCases_on `nsid` >>
      irule body_structlit_case_full >> rpt strip_tac >>
      irule every_body_expr_full_ok >> simp[EVERY_MEM, MEM_MAP, EXISTS_PROD] >>
      rpt strip_tac >> first_x_assum irule >>
      conj_tac
      >- (drule expr_struct_field_bound >> simp[]) >>
      first_x_assum irule >> simp[MEM_MAP, EXISTS_PROD] >>
      qexists_tac `p_1` >> simp[])
  >~ [`body_expr_full_ok _ (TypeBuiltin _ _ _ _)`]
  >- (irule body_type_builtin_case_full >> rpt strip_tac >>
      irule every_body_expr_full_ok >> simp[EVERY_MEM] >>
      rpt strip_tac >> first_x_assum irule >>
      drule expr_list_member_bound >> simp[expr_size_def]) >>
  rename1 `Builtin ann bt es` >>
  `EVERY (body_expr_full_ok cx) es` by
    (simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
     rpt conj_tac >- (drule expr_list_member_bound >> simp[expr_size_def]) >>
     metis_tac[constant_expr_runtime_constant]) >>
  `!ct addr. code_slice_source bt es <> SOME (ct,addr)` by
    (simp[code_slice_source_SOME] >> rpt strip_tac >>
     gvs[runtime_constant_builtin_def, constant_builtin_def]) >>
  irule body_builtin_case_full >> rpt strip_tac >> gvs[every_body_expr_full_ok] >>
  Cases_on `es` >> fs[builtin_args_length_ok_def, type_check_def, assert_def]
QED

Theorem runtime_constant_expr_no_mutation[local]:
  runtime_constant_expr mods e ==> ~expr_can_mutate ce e
Proof
  completeInduct_on `expr_size e` >> Cases_on `e` >> rpt strip_tac >>
  gvs[PULL_FORALL, runtime_constant_expr_def, expr_can_mutate_def,
      named_exprs_can_mutate_map, exprs_can_mutate_exists, EVERY_MEM, EXISTS_MEM]
  >~ [`MEM _ (MAP SND _)`] >-
    (qpat_assum `MEM e (MAP SND l)` mp_tac >>
     PURE_REWRITE_TAC [MEM_MAP, EXISTS_PROD] >> strip_tac >>
     `expr_size e < type_size t +
       (list_size (pair_size (list_size char_size) expr_size) l +
        (pair_size (option_size (\x. x)) (list_size char_size) p + 1))` by
       (Cases_on `y` >> fs[] >> drule expr_struct_field_bound >> simp[]) >>
     metis_tac[]) >>
  qpat_assum `MEM e l` (mp_tac o MATCH_MP expr_list_member_bound) >>
  strip_tac >>
  qpat_assum `!e. expr_size e < _ ==> _` (qspec_then `e` mp_tac) >>
  impl_tac >- decide_tac >>
  asm_rewrite_tac[] >>
  qpat_assum `!e. _ /\ (MEM e l ==> _)` (qspec_then `e` mp_tac) >>
  simp[] >> metis_tac[constant_expr_runtime_constant]
QED

Theorem runtime_default_expr_full:
  runtime_constant_expr mods e /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env e es /\
  expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,fn,shadow_fn)
    ce cx ty e es (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,fn,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t.
      expr_sim_full_post (DF,lo,d,ctx,fn) ce cx e (es,sa,sb,s0,op,G0,tn0)
        H res ee G tn t /\
      ~t.vs_halted /\ ee.scopes = es.scopes /\ expr_sim_inv ce cx env ee /\
      !v. res = INL v ==> expr_result_typed env e (Value v))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `body_expr_full_ok cx e` by metis_tac[runtime_constant_expr_body_full_ok] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,fn,shadow_fn) ce cx ty e es` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  qpat_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE[expr_sim_full_via_bundle]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,
    `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  asm_rewrite_tac[] >> disch_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >> asm_rewrite_tac[] >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp_tac (srw_ss()) [] >> disch_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) = (res,ee)` by
    asm_rewrite_tac[] >>
  `expr_body_pre ce cx env e (es with gas_obs := xs)` by simp[expr_body_pre_gas_obs] >>
  mp_tac (Q.SPECL [`ce`,`cx`,`env`,`e`,`es with gas_obs := xs`,`res`,`ee`]
    exprSimSourceTheory.expr_body_pre_eval) >>
  impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `bind _ _ _ = (res,ee)` mp_tac >>
     simp_tac (srw_ss()) [ETA_AX, vyperStateTheory.bind_def]) >>
  strip_tac >> asm_rewrite_tac[] >>
  `~expr_can_mutate ce e` by metis_tac[runtime_constant_expr_no_mutation] >>
  Cases_on `eval_expr cx e (es with gas_obs := xs)` >>
  rename1 `_ = (result,es_eval)` >>
  `es_eval.scopes = es.scopes` by
    (mp_tac (Q.SPECL [`ce`,`cx`,`e`,`es with gas_obs := xs`,`result`,`es_eval`]
       eval_expr_no_mutation_scopes) >>
     asm_rewrite_tac[] >> simp[]) >>
  Cases_on `result`
  >- (`read_result cx x es_eval = (res,ee)` by
       (qpat_assum `eval_expr _ _ _ = (INL x,es_eval)` (fn ev =>
          qpat_assum `bind _ _ _ = (res,ee)`
            (ACCEPT_TAC o SIMP_RULE (srw_ss()) [vyperStateTheory.bind_def, ev]))) >>
      drule read_result_scopes >> simp[]) >>
  `es_eval = ee` by
    (qpat_assum `eval_expr _ _ _ = (INR y,es_eval)` (fn ev =>
       qpat_assum `bind _ _ _ = (res,ee)` (mp_tac o SIMP_RULE (srw_ss())
         [vyperStateTheory.bind_def, ev, pairTheory.PAIR_EQ])) >>
     simp[]) >>
  qpat_assum `es_eval = ee` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC
QED
