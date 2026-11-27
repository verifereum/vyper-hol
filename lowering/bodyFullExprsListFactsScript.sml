Theory bodyFullExprsListFacts
Ancestors bodyFullPreds
  bodyFullPredsMods[qualified]

Theorem body_exprs_full_ok_nil:
  !cx. body_exprs_full_ok_mods mods exps cx [] = T
Proof
  simp[CONJUNCT1 body_exprs_full_ok_def]
QED

Theorem body_exprs_full_ok_cons:
  !cx e es.
    body_exprs_full_ok_mods mods exps cx (e::es) =
      (body_expr_full_ok_mods mods exps cx e /\
       ((?s tv t s1 v t1.
           eval_expr cx e s = (INL tv,t) /\
           read_result cx tv s1 = (INL v,t1)) ==>
        body_exprs_full_ok_mods mods exps cx es))
Proof
  rpt gen_tac >>
  pure_once_rewrite_tac[CONJUNCT2 body_exprs_full_ok_def] >>
  REFL_TAC
QED
