Theory bodyFullRangeProjection
Ancestors bodyFullPreds

Theorem body_iterator_full_ok_range:
  !cx e1 e2. body_iterator_full_ok cx (Range e1 e2) ==>
    body_expr_full_ok cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv,t) /\
                       read_result cx tv s1 = (INL v,t1)) ==>
     body_expr_full_ok cx e2)
Proof
  simp[body_iterator_full_ok_def]
  >> (metis_tac[])
QED
