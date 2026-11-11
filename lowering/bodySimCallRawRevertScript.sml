(* Piece of bodySimCallCases.body_raw_revert_case. *)

Theory bodySimCallRawRevert
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph
  exprSimHypsDefs exprSimRawRevertCore

(* raw_revert's operand may contain internal calls: its own body case gives
   the operand's simulation, and raw_revert_vv_sim lifts it. *)
Theorem raw_revert_body_expr_ok:
  !cx v22 es v23.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v22 RawRevert es v23)
Proof
  rpt strip_tac >> match_mp_tac body_expr_ok_intro >> conj_tac >- gvs[] >> simp[] >> rw[] >>
  `expr_vv_case F ctx func cenv cx (Call v22 RawRevert es v23)` by
    (rw[expr_vv_case_def] >>
     drule raw_revert_pre_arg >> strip_tac >> gvs[] >>
     irule raw_revert_vv_sim >>
     gvs[body_exprs_ok_def, body_expr_ok_def] >> metis_tac[]) >>
  drule_at (Pos last) expr_sim_case_of_vv >> simp[] >> strip_tac >>
  fs[expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED
