Theory bodyPtrBopInMixedAdapter
Ancestors bodyPtrBopInMixed bodyPtrBopInSourceOrigin exprSimOperators
  exprBopSimProps vyperState

Theorem membership_mixed_source_adapter:
  lower_value compile_expr cenv (expr_type e1) e1 sa = (needle,sc) ==>
  compile_expr cenv (expr_type e2) e2 sc = (vv,sm) ==>
  body_exprs_ptr_ok cx [e1;e2] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  is_word_type (expr_type e1) /\
  bop_operand_entry d ctx fn cenv cx e1 es sa sc needle s0 G0 tn0 /\
  (!v1 es1 s1 G1 tn1.
    bop_operand_post d ctx fn cenv cx e1 es sa sc needle s0 G0 tn0 v1 es1 s1 G1 tn1 /\
    (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) = (INL v1,es1)) /\
    es1.gas_obs = [] /\ ~s1.vs_halted ==>
    membership_vv_entry d ctx fn cenv cx e2 es1 sc sm s1 G1 tn1) /\
  (!v1 es1 s1 G1 tn1 tv es2 s2 G2 tn2.
    bop_operand_post d ctx fn cenv cx e1 es sa sc needle s0 G0 tn0 v1 es1 s1 G1 tn1 /\
    membership_vv_post d ctx fn cenv cx e2 es1 sc sm vv s1 G1 tn1 tv es2 s2 G2 tn2 /\
    (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) = (INL v1,es1)) /\
    (?gs. eval_expr cx e2 (es1 with gas_obs := gs) = (INL tv,es2)) /\
    es1.gas_obs = [] /\ ~s1.vs_halted /\ es2.gas_obs = [] /\ ~s2.vs_halted ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
      (bind (read_result cx tv) (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st)))
      (es2,s2,G2,tn2) Q (\res ee gt r. expr_exit res r)) /\
  (!marks err ee leaf sf.
    gas_exempt_cert F (cx_tops cx) (ctx,fn)
      (ignore_bind (bind (eval_expr cx e1) (read_result cx)) (return ()))
      (es,s0) marks (err,ee) (leaf,sf) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,fn)
      (bind (bind (eval_expr cx e1) (read_result cx)) (\v1.
       ignore_bind (bind (eval_expr cx e2) (\tv. bind (read_result cx tv)
         (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st)))) (return ())))
      (es,s0) marks (err,ee) (leaf,sf)) /\
  (!left v1 mid t right err ee leaf sf.
    gas_marked_exec F (ctx,fn) (bind (eval_expr cx e1) (read_result cx))
      (es,s0) left (INL v1) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,fn)
      (ignore_bind (bind (eval_expr cx e2) (\tv. bind (read_result cx tv)
        (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st)))) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,sf) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,fn)
      (bind (bind (eval_expr cx e1) (read_result cx)) (\v1.
       ignore_bind (bind (eval_expr cx e2) (\tv. bind (read_result cx tv)
         (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st)))) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,sf)) /\
  (!v1 es1 s1 G1 tn1.
    bop_operand_post d ctx fn cenv cx e1 es sa sc needle s0 G0 tn0 v1 es1 s1 G1 tn1 /\
    (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) = (INL v1,es1)) /\
    es1.gas_obs = [] /\ ~s1.vs_halted ==>
    (!marks err ee leaf sf.
      gas_exempt_cert F (cx_tops cx) (ctx,fn)
        (ignore_bind (eval_expr cx e2) (return ())) (es1,s1) marks (err,ee) (leaf,sf) ==>
      gas_exempt_cert F (cx_tops cx) (ctx,fn)
        (bind (eval_expr cx e2) (\tv. ignore_bind (bind (read_result cx tv)
          (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st))) (return ())))
        (es1,s1) marks (err,ee) (leaf,sf)) /\
    (!left tv mid t right err ee leaf sf.
      gas_marked_exec F (ctx,fn) (eval_expr cx e2) (es1,s1) left (INL tv) mid (OK t) /\
      gas_exempt_cert F (cx_tops cx) (ctx,fn)
        (ignore_bind (bind (read_result cx tv)
          (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st))) (return ()))
        (mid with gas_obs := [],t) right (err,ee) (leaf,sf) ==>
      gas_exempt_cert F (cx_tops cx) (ctx,fn)
        (bind (eval_expr cx e2) (\tv. ignore_bind (bind (read_result cx tv)
          (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st))) (return ())))
        (es1,s1) (left ++ right) (err,ee) (leaf,sf))) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (bind (eval_expr cx e1) (read_result cx)) (\v1.
      bind (eval_expr cx e2) (\tv. bind (read_result cx tv)
        (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st)))))
    (es,s0,G0,tn0) Q (\res ee gt r. expr_exit res r)
Proof
  rpt disch_tac >>
  drule_at_then (Pat `lower_value _ _ _ _ _ = _`)
    (fn th => first_assum (mp_then (Pat `compile_expr _ _ _ _ = _`)
      (irule o BETA_RULE o
       Q.INST [`p1` |-> `bind (eval_expr cx e1) (read_result cx)`,
         `p2` |-> `eval_expr cx e2`] o
       Q.ISPEC `\v1 tv. bind (read_result cx tv)
         (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st))` o
       Q.GEN `next` o SPEC_ALL) th))
    (Q.INST [`P1` |-> `\rr ee. ?gs. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gs) = (rr,ee)`,
     `P2` |-> `\v1 es1 rr ee. ?gs. eval_expr cx e2
      (es1 with gas_obs := gs) = (rr,ee)`] membership_mixed_outcome_ptr) >>
  fs[] >>
  `!v ee. (?gs. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gs) = (INL v,ee)) ==>
      expr_sim_inv cenv cx env ee` by
    (drule expr_body_pre_bop >> strip_tac >> rpt gen_tac >> disch_tac >>
     drule_all membership_needle_origin_success >> simp[]) >>
  simp[] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists_tac `tops` >> simp[]) >>
  conj_tac >- (qexists_tac `env` >> simp[] >> first_assum ACCEPT_TAC) >>
  qexists_tac `d` >> simp[] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
  metis_tac[]
QED

Theorem membership_source_bind:
  bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx) =
  bind (bind (eval_expr cx e1) (read_result cx)) (\v1.
    bind (eval_expr cx e2) (\tv. bind (read_result cx tv)
      (\v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st))))
Proof
  rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind, vyperStateTheory.bind_assoc]
QED
