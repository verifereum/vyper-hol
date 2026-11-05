(*
 * Pop on a nested target: body_pop_nested_target_frag, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory bodyPopNestedTargetFrag
Ancestors
  exprSimPopNestedBase
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* RESIDUAL (target metadata): the target's fragment judgment in the body,
   where an index may make an internal call.  target_case_all gives
   target_sim from body_base_target_ok's index judgments and target_pre,
   whose target_env_ok asks for every module's storage and mapping
   declarations to be in the compile environment's tables, which body_inv
   gives for the main module only (exprSimPopNested's
   pop_nested_expr_target_frag has the same gap). *)
Theorem body_pop_nested_target_frag:
  !cx bt tops ctx func cenv env ann es.
    body_base_target_ok cx bt /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  cheat
QED
