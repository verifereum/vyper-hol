(*
 * Pop on a nested target: body_pop_nested_target_frag, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory bodyPopNestedTargetFrag
Ancestors
  exprSimPopNestedBase popTargetPre targetPlaceSimCasesBase exprSimHypsDefs
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* In a body, the indices' judgments of a target, internal calls allowed:
   body_base_target_ok gives body_expr_ok for each index whose base place
   evaluates, and body_inv turns it into the index's cases. *)
Theorem body_target_idx_case:
  !bt cx tops ctx func cenv.
    body_inv tops ctx cenv cx /\ body_base_target_ok cx bt ==>
    target_idx_case F ctx func cenv cx bt
Proof
  recInduct base_assignment_target_induct >>
  rw[target_idx_case_def, body_base_target_ok_def] >>
  gvs[body_expr_ok_def, expr_sim_case_def, expr_vv_case_def] >>
  metis_tac[]
QED

(* The target's fragment judgment in the body, where an index may make an
   internal call: target_case_all gives target_sim from body_base_target_ok's
   index judgments, at the target_pre the pop's expr_body_pre gives. *)
Theorem body_pop_nested_target_frag:
  !cx bt tops ctx func cenv env ann es.
    body_base_target_ok cx bt /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  rpt strip_tac >> irule pop_target_frag_of_sim >>
  `target_case F ctx func cenv cx bt` by
    metis_tac[target_case_all, body_target_idx_case] >>
  fs[target_case_def] >> first_x_assum irule >>
  metis_tac[target_pre_of_pop]
QED
