Theory bodyPtrBopPairCps
Ancestors
  bodyPtrBopOperandContract bodyPtrBopOperands exprSimOperators
  vyperInterpreter vyperState

Theorem bop_source_success_parts[local]:
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  ?tv mid. eval_expr cx e es = (INL tv,mid) /\
           read_result cx tv mid = (INL v,ee)
Proof
  simp[bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem bop_pair_outcome_ptr:
  p1 = bind (eval_expr cx e1) (read_result cx) /\
  p2 = bind (eval_expr cx e2) (read_result cx) /\
  body_exprs_ptr_ok cx [e1;e2] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  lower_value compile_expr cenv ty1 e1 sa = (x,sb) /\
  lower_value compile_expr cenv ty2 e2 sb = (y,sc) /\
  bop_operand_entry d ctx func cenv cx e1 es sa sb x s0 G0 tn0 /\
  (!gs rr ee. p1 (es with gas_obs := gs) = (rr,ee) ==> P1 rr ee) /\
  (!v ee. P1 (INL v) ee ==> expr_sim_inv cenv cx env ee) /\
  (!v1 es1 s1 G1 tn1.
    bop_operand_post d ctx func cenv cx e1 es sa sb x s0 G0 tn0
      v1 es1 s1 G1 tn1 /\
    P1 (INL v1) es1 /\ es1.gas_obs = [] /\ ~s1.vs_halted ==>
    bop_operand_entry d ctx func cenv cx e2 es1 sb sc y s1 G1 tn1 /\
    (!gs rr ee. p2 (es1 with gas_obs := gs) = (rr,ee) ==>
      P2 v1 es1 rr ee)) /\
  (!v1 es1 s1 G1 tn1 v2 es2 s2 G2 tn2.
    bop_operand_post d ctx func cenv cx e1 es sa sb x s0 G0 tn0
      v1 es1 s1 G1 tn1 /\
    bop_operand_post d ctx func cenv cx e2 es1 sb sc y s1 G1 tn1
      v2 es2 s2 G2 tn2 /\
    P1 (INL v1) es1 /\ P2 v1 es1 (INL v2) es2 /\
    es1.gas_obs = [] /\ ~s1.vs_halted /\
    es2.gas_obs = [] /\ ~s2.vs_halted ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next v1 v2) (es2,s2,G2,tn2) Q (\res ee gt r. expr_exit res r)) /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func) (ignore_bind p1 (return ()))
      (es,s0) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind p1 (\v1. ignore_bind (bind p2 (next v1)) (return ())))
      (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left v1 mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func) p1 (es,s0) left (INL v1) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (bind p2 (next v1)) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind p1 (\v1. ignore_bind (bind p2 (next v1)) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,fstate)) /\
  (!v1 es1 s1 G1 tn1.
    bop_operand_post d ctx func cenv cx e1 es sa sb x s0 G0 tn0
      v1 es1 s1 G1 tn1 /\
    P1 (INL v1) es1 /\ es1.gas_obs = [] /\ ~s1.vs_halted ==>
    (!marks err ee leaf fstate.
      gas_exempt_cert F (cx_tops cx) (ctx,func) (ignore_bind p2 (return ()))
        (es1,s1) marks (err,ee) (leaf,fstate) ==>
      gas_exempt_cert F (cx_tops cx) (ctx,func)
        (bind p2 (\v2. ignore_bind (next v1 v2) (return ())))
        (es1,s1) marks (err,ee) (leaf,fstate)) /\
    (!left v2 mid t right err ee leaf fstate.
      gas_marked_exec F (ctx,func) p2 (es1,s1) left (INL v2) mid (OK t) /\
      gas_exempt_cert F (cx_tops cx) (ctx,func)
        (ignore_bind (next v1 v2) (return ()))
        (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
      gas_exempt_cert F (cx_tops cx) (ctx,func)
        (bind p2 (\v2. ignore_bind (next v1 v2) (return ())))
        (es1,s1) (left ++ right) (err,ee) (leaf,fstate))) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind p1 (\v1. bind p2 (next v1))) (es,s0,G0,tn0)
    Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> gvs[] >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty1 e1 es` by
    (fs[body_exprs_ptr_ok_pair, bodyPtrPredsTheory.body_expr_ptr_ok_def] >>
     metis_tac[]) >>
  irule bop_operand_contract_ptr >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `\rr ee. P1 rr ee /\
    (!v. rr = INL v ==> ?gs tv mid.
      eval_expr cx e1 (es with gas_obs := gs) = (INL tv,mid) /\
      read_result cx tv mid = (INL v,ee))` >>
  qpat_assum `bop_operand_entry _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  qpat_assum `lower_value _ _ _ _ sa = _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
      metis_tac[bop_source_success_parts]) >>
  map_every qx_gen_tac [`v1`, `es1`, `G1`, `tn1`, `s1`] >> strip_tac >>
  `expr_sim_inv cenv cx env es1` by metis_tac[] >>
  `expr_sim_ptr d ctx PG func cenv cx ty2 e2 es1` by
    (fs[body_exprs_ptr_ok_pair, bodyPtrPredsTheory.body_expr_ptr_ok_def] >>
     metis_tac[]) >>
  `bop_operand_entry d ctx func cenv cx e2 es1 sb sc y s1 G1 tn1 /\
   (!gs rr ee. bind (eval_expr cx e2) (read_result cx)
      (es1 with gas_obs := gs) = (rr,ee) ==> P2 v1 es1 rr ee)` by
    metis_tac[] >>
  irule bop_operand_contract_ptr >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `P2 v1 es1` >>
  qpat_assum `bop_operand_entry _ _ _ _ _ e2 _ _ _ _ _ _ _`
    (irule_at Any) >>
  qpat_assum `lower_value _ _ _ e2 _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED
