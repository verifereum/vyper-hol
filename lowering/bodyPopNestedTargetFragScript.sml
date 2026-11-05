(*
 * Pop on a nested target: body_pop_nested_target_frag, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory bodyPopNestedTargetFrag
Ancestors
  exprSimPopNestedBase popTargetPre exprSimPopImmutableTarget
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

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
