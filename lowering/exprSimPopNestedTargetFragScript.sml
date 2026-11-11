(*
 * Pop on a nested target: pop_nested_expr_target_frag, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedTargetFrag
Ancestors
  exprSimPopNestedBase targetPlaceSimCasesBase exprSimHypsDefs allocLimits
  supportedExprTraverse popTargetPre
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* The target's fragment judgment at the expression level: target_case_all
   gives target_sim from the indices' judgments (expr_ok, below the pop's
   size) and target_pre (static, from expr_sim_pre). *)
Theorem pop_nested_expr_target_frag:
  !cenv ann bt ctx func cx env es.
    expr_sim_below cenv (expr_size (Pop ann bt)) /\
    expr_sim_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  rpt strip_tac >> irule pop_target_frag_of_sim >>
  gvs[expr_sim_pre_def, int_calls_expr_def] >>
  `target_case T ctx func cenv cx bt` by
    (irule target_case_all >> irule target_idx_case_ok >>
     rw[] >> fs[expr_sim_below_def] >> first_x_assum irule >>
     imp_res_tac nested_pop_index_size >> simp[expr_size_def]) >>
  fs[target_case_def] >> first_x_assum irule >>
  simp[] >> irule target_pre_of_pop >> simp[] >>
  qexists_tac `ann` >>
  simp[expr_body_pre_def, int_calls_expr_def]
QED
