(* The linked source post of a runtime-constant default. *)
Theory linkedRuntimeDefaultExpression
Ancestors
  gasOutcomeFullModsSource runtimeDefaultExpression bodySimStmtFacts
  abiEncodeArgsScopes vyperScopePreservation exprSimHypsDefs
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  vyperInterpreter vyperState venomState

Theorem runtime_default_expr_post_mods:
  runtime_constant_expr mods e /\ expr_body_pre_mods mods ce cx env e es /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G' tn' u.
      Q H res ee G' tn' u /\ ~u.vs_halted /\ ee.scopes = es.scopes /\
      expr_sim_inv_mods mods ce cx env ee /\
      !v. res = INL v ==> expr_result_typed env e (Value v))
    R
Proof
  strip_tac >>
  irule gas_outcome_full_mods_post_source >> goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >> asm_rewrite_tac[] >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp_tac (srw_ss()) [] >> disch_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) = (res,ee)` by
    asm_rewrite_tac[] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := xs)` by
    (qpat_assum `expr_body_pre_mods mods ce cx env e es` mp_tac >>
     PURE_REWRITE_TAC [expr_body_pre_mods_def, expr_sim_inv_mods_def,
       gas_obs_type_invariants, evaluation_state_accfupds] >>
     disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`mods` |-> `mods`, `cenv` |-> `ce`,
    `es` |-> `es with gas_obs := xs`, `es'` |-> `ee`]
    (SPEC_ALL expr_body_pre_eval_mods)) >>
  impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `bind _ _ _ = (res,ee)` mp_tac >>
     simp_tac (srw_ss()) [ETA_AX, vyperStateTheory.bind_def]) >>
  strip_tac >> asm_rewrite_tac[] >>
  conj_tac >| [ALL_TAC,
    rpt strip_tac >> gvs[expr_result_typed_def, expr_runtime_typed_def,
                         value_runtime_typed_def, value_result_typed_def]] >>
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
