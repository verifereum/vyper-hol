(*
 * The external-call case of the full body induction: target, positional
 * arguments and keyword arguments over the finite-horizon joint judgment.
 *
 * Composed from the three stages: bodyFullExtCallRequest (operands and
 * request), bodyFullExtCallStep (the call) and bodyFullExtCallReturn
 * (return handling).
 *
 * TOP-LEVEL:
 *   extcall_expr_full_ok
 *)
Theory bodyFullExtCall
Ancestors
  bodyFullExtCallRequest bodyFullExtCallStep bodyFullExtCallReturn
  bodyFullExtCallCompose
  bodyFullPreds bodyFullOfVV
  gasShadowCompile gasOutcomeFullCompose bodySimFull exprLowering compileEnv context pair
  vyperInterpreter vyperAST list

val _ = Parse.hide "body";

Theorem extcall_value_from_vv_full:
  !cx ann is_static skip sig opts args dflt.
  (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip sig opts) args dflt) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann (ExtCall is_static skip sig opts) args dflt) es) ==>
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip sig opts) args dflt) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann (ExtCall is_static skip sig opts) args dflt) es
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
  simp[vyperASTTheory.expr_type_def, optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `rty` assume_tac) >>
  irule bodyFullOfVVTheory.expr_sim_full_of_vv >>
  simp[loweringPostsTheory.post_value_type_def, vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (drule aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound >>
      simp[vyperASTTheory.expr_type_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `vyperState$bind
         (eval_expr cx (Call ann (ExtCall is_static' skip sig opts) args dflt))
         (\result. read_result cx result) (es with gas_obs := gs) = (INL v,ee)` by
        simp[vyperStateTheory.bind_def] >>
      drule_at (Pat `vyperState$bind _ _ _ = _`)
        vyperTypeEvalSoundnessTheory.eval_expr_read_type_sound >>
      disch_then (qspec_then `env` mp_tac) >>
      gvs[exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          vyperASTTheory.expr_type_def] >> strip_tac >>
      gvs[vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem extcall_expr_full_ok:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_full_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_full_ok cx (TAKE 1 es) ==>
    body_expr_full_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (irule extcall_value_from_vv_full >>
      metis_tac[extcall_vv_full_ok]) >>
  metis_tac[extcall_vv_full_ok]
QED
