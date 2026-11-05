(*
 * Pop on a nested target: pop_nested_local_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedLocal
Ancestors
  exprSimPopNestedBase exprSimPopNestedLocalPopped
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* Pop on an array inside a memory local, the local itself included
   (x.pop(), x.a.pop(), x[i].pop()).  The run is compile_pop_name_sim's at
   the target's pointer: the pop stores the array's new length word inside
   the local's region, which locals_kept exempts (dynarray_len_at), and the
   result is the element's pointer, read back through the popped history.
   A place the target's own index left dead in the local's value (it popped
   an ancestor) is read from the history; its memory comes from the
   admitted pop_local_popped_in_memory. *)
Theorem pop_nested_local_sim:
  !ctx func cenv cx env ann bt ty es id.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED
