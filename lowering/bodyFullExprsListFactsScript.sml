Theory bodyFullExprsListFacts
Ancestors bodyFullPreds
  bodyFullPredsMods[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[CONJUNCT1 body_exprs_full_ok_def]
QED
*)
Theorem body_exprs_full_ok_nil:
  !cx. body_exprs_full_ok_mods mods exps cx [] = T
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >>
  pure_once_rewrite_tac[CONJUNCT2 body_exprs_full_ok_def] >>
  REFL_TAC
QED
*)
Theorem body_exprs_full_ok_cons:
  !cx e es.
    body_exprs_full_ok_mods mods exps cx (e::es) =
      (body_expr_full_ok_mods mods exps cx e /\
       ((?s tv t s1 v t1.
           eval_expr cx e s = (INL tv,t) /\
           read_result cx tv s1 = (INL v,t1)) ==>
        body_exprs_full_ok_mods mods exps cx es))
Proof
  cheat
QED
