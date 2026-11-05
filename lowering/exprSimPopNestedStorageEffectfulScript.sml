(*
 * Pop on a nested target: pop_nested_storage_effectful_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedStorageEffectful
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

(* RESIDUAL (effectful storage indices): an index that pops or calls can
   shrink an array the target already points into, so the header the pop
   reads can be dead.  Source and Venom read the same raw slot, but
   stmt_state_rel relates only live storage.  Needs raw agreement on slots
   made dead by a pop.  The AugAssign on a storage place with an
   effectful index, and targetPlaceSimCases' target_subscript_case, have
   the same exposure. *)
Theorem pop_nested_storage_effectful_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED
