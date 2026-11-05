(*
 * Pop on a nested target: pop_nested_storage_effectful_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedStorageEffectful
Ancestors
  exprSimPopNestedBase exprSimPopNestedStorageFrame
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* RESIDUAL (indices that may change storage): an index that pops a
   storage array or calls can shrink an array the target already points
   into, so the header the pop reads can be dead.  Example: with
     b: DynArray[DynArray[DynArray[uint256, 2], 2], 2] = [[[7]], [[0], [0]]]
   the expression self.b[1][self.b.pop()[0][0]].pop() bounds-checks b[1]
   while b has length 2, then the index pops b (length 1), so b[1] and the
   header of b[1][0] are dead when the outer pop reads it.  Source and
   Venom read the same raw slot, but stmt_state_rel after the index relates
   only live storage, and expr_post has no Venom storage frame for dead
   slots, so the two header loads can't be shown equal.  Waits on the
   shared dead-slot storage frame (raw agreement on slots made dead by a
   pop or a call).  The AugAssign on a storage place with an effectful
   index, and targetPlaceSimCases' target_subscript_case, have the same
   exposure.  Indices that leave storage alone are
   pop_nested_storage_frame_sim (exprSimPopNestedStorageFrame). *)
Theorem pop_nested_storage_effectful_dead_case:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) /\
    ~EVERY (storage_frame_expr cx) (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

Theorem pop_nested_storage_effectful_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >>
  Cases_on `EVERY (storage_frame_expr cx) (target_indices bt)`
  >- (irule pop_nested_storage_frame_sim >> metis_tac[]) >>
  irule pop_nested_storage_effectful_dead_case >> metis_tac[]
QED
