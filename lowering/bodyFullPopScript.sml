Theory bodyFullPop
Ancestors
  bodyFullTarget bodyFullTargetDefs bodyFullPreds bodySimFull bodyFullOfVV
  gasOutcomeFullCompose gasOutcomeFull gasShadowCompile gasShadowState
  popTargetPre exprSimHyps exprSimHypsDefs exprSimSource exprSimPopNestedBase
  exprLoweringProps loweringPosts exprLowering compileEnv
  vyperInterpreter vyperState vyperAST

val _ = Parse.hide "body";

Theorem pop_full_target_pre[local]:
  !cenv cx env ann bt es.
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    target_pre cenv cx env bt es
Proof
  rpt strip_tac >> irule target_pre_of_pop >>
  reverse conj_tac >- (qexists `ann` >> simp[]) >>
  strip_tac >> gvs[targetPlaceSimTheory.immutable_root_def] >>
  drule pop_immutable_root_rejected >>
  disch_then drule >> simp[]
QED

(* The target producer selects one endpoint with its place and pointer.
   The pop suffix reads and updates the dynamic length at that pointer. *)
Theorem pop_expr_full_ok:
  !cx v10 bt. body_base_target_full_ok cx bt ==> body_expr_full_ok cx (Pop v10 bt)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac
QED
