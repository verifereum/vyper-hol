(* Piece of bodySimCallCases.body_selfdestruct_case. *)

Theory bodySimCallSelfDestruct
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph
  exprSimHypsDefs exprSimSelfDestruct

(* selfdestruct's operand may contain internal calls: its own body case
   gives the operand's simulation, and selfdestruct_vv_sim lifts it. *)
Theorem selfdestruct_body_expr_ok:
  !cx v24 es v25.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  rpt strip_tac >> match_mp_tac body_expr_ok_intro >> conj_tac >- gvs[] >> simp[] >> rw[] >>
  `expr_vv_case F ctx func cenv cx (Call v24 SelfDestructTarget es v25)` by
    (rw[expr_vv_case_def] >>
     drule selfdestruct_pre_arg >> strip_tac >> gvs[] >>
     irule selfdestruct_vv_sim >>
     gvs[body_exprs_ok_def, body_expr_ok_def] >> metis_tac[]) >>
  drule_at (Pos last) expr_sim_case_of_vv >> simp[] >> strip_tac >>
  fs[expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED
