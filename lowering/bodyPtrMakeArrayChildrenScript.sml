(* Conditional operand judgments are unlocked only by successful source runs. *)
Theory bodyPtrMakeArrayChildren
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim gasSummaryComposePtr vyperState
  vyperInterpreter list

Theorem literal_body_child_vv:
  body_exprs_ptr_ok cx (e::args) /\ body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es ==>
  expr_vv_sim_ptr d ctx PG func ce cx ty e es
Proof
  simp[body_exprs_ptr_ok_def] >>
  rpt strip_tac >> fs[Once body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem literal_marked_children_tail:
  body_exprs_ptr_ok cx (e::args) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) ee G tn (OK t) ==>
  body_exprs_ptr_ok cx args
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v,ee with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  fs[body_exprs_ptr_ok_def, bind_def, AllCaseEqs()] >> metis_tac[]
QED
