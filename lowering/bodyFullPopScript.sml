Theory bodyFullPop
Ancestors
  bodyFullTarget bodyFullTargetDefs bodyFullPreds bodySimFull bodyFullOfVV
  gasOutcomeFullCompose gasOutcomeFull gasShadowCompile gasShadowState
  popTargetPre exprSimHyps exprSimHypsDefs exprSimSource exprSimPopNestedBase
  exprLoweringProps loweringPosts exprLowering compileEnv
  vyperInterpreter vyperState vyperAST

val _ = Parse.hide "body";

(* The target producer selects one endpoint with its place and pointer.
   The pop suffix reads and updates the dynamic length at that pointer. *)
Theorem pop_expr_full_ok:
  !cx v10 bt. body_base_target_full_ok cx bt ==> body_expr_full_ok cx (Pop v10 bt)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac
QED
