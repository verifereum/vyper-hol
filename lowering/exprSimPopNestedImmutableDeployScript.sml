(*
 * Pop on a nested target: pop_nested_immutable_deploy_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedImmutableDeploy
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

(* RESIDUAL (constructor immutables): pop on a member of an immutable in
   the constructor, which Python's checker accepts for a complex immutable
   (local.py skips the modification count when var_info is None).  The
   lowering loads and stores the length through the immutables buffer
   (compile_ptr_load/compile_ptr_store), and immutable_holds accepts the
   code pointer to the popped element, whose bytes the pop leaves in the
   buffer.  The proof also needs the constructor immutable invariant. *)
Theorem pop_nested_immutable_deploy_sim:
  !ctx func cenv cx env ann bt ty es src id.
    cx.in_deploy /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED
