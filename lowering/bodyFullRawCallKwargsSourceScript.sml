(* Normal source-state transport for raw_call keyword evaluation. *)
Theory bodyFullRawCallKwargsSource
Ancestors
  rawCallShapePtr exprSimSource exprSimWordArgs
  vyperEvalExprPreservesScopesDom

Theorem raw_call_kwargs_source_inv:
  !cenv cx env ann flags args dflt base kws es vs ee.
    expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) base /\
    expr_sim_inv cenv cx env es /\ EVERY (\e. MEM e args) kws /\
    eval_exprs cx kws es = (INL vs,ee) ==>
    expr_sim_inv cenv cx env ee /\ MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  ntac 8 gen_tac >> Induct
  >- simp[eval_exprs_nil] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  reverse conj_tac
  >- metis_tac[eval_exprs_preserves_scopes_dom] >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[AllCaseEqs()] >>
  `expr_body_pre cenv cx env h es` by
    metis_tac[rawCallShapePtrTheory.expr_body_pre_raw_call_arg] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
  metis_tac[]
QED
