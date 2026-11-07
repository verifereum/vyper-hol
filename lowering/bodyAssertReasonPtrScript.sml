(* Source-state bridge used by the body-level assert-with-reason case. *)
Theory bodyAssertReasonPtr
Ancestors
  assertReasonTypedPtr bodyPtrPreds bodyPtrDefs bodySim bodyExprPreFacts
  exprSimSource exprSimHypsDefs exprSimDefs vyperInterpreter vyperState
Libs
  monadsyntax

Theorem assert_reason_body_endpoint_ptr:
  (!s tv t. eval_expr cx e s = (INL tv,t) ==> body_expr_ptr_ok cx r) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ expr_body_pre cenv cx env r es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL (BoolV F),es1) ==>
  expr_body_pre cenv cx env r es1 /\
  expr_vv_sim_ptr d ctx PG fn cenv cx (expr_type r) r es1
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule exprSimSourceTheory.expr_body_pre_eval >>
  disch_then (qspecl_then [`INL (BoolV F)`,`es1`] mp_tac) >>
  (impl_tac >- fs[bind_def]) >> strip_tac >>
  `expr_body_pre cenv cx env r es1` by fs[expr_body_pre_def] >>
  `?tv t. eval_expr cx e (es with gas_obs := gs) = (INL tv,t)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_expr_ptr_ok cx r` by metis_tac[] >>
  simp[] >> fs[body_expr_ptr_ok_def] >> metis_tac[]
QED
