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
   (x.pop(), x.a.pop(), x[i].pop()), when every evaluation of the target
   leaves its place live in the local's value or unreadable.  The run is
   compile_pop_name_sim's at the target's pointer: the pop stores the
   array's new length word inside the local's region, which locals_kept
   exempts (dynarray_len_at), and the result is the element's pointer,
   read back through the popped history. *)
Theorem pop_nested_local_live_case:
  !ctx func cenv cx env ann bt ty es id.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id /\
    (!s path t entry err.
       eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
       lookup_scopes id t.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INR err ==>
       read_popped entry.type path entry.popped = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* By whether some evaluation of the target leaves its place reading a
   popped snapshot (pop_nested_local_popped_case) or none does. *)
Theorem pop_nested_local_sim:
  !ctx func cenv cx env ann bt ty es id.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >>
  Cases_on `?s path t entry err v.
              eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
              lookup_scopes id t.scopes = SOME entry /\
              evaluate_subscripts entry.type entry.value path = INR err /\
              read_popped entry.type path entry.popped = SOME v`
  >- (fs[] >> metis_tac[pop_nested_local_popped_case]) >>
  `!s path t entry err.
     eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
     lookup_scopes id t.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INR err ==>
     read_popped entry.type path entry.popped = NONE` by
    (rpt strip_tac >>
     Cases_on `read_popped entry.type path entry.popped` >> fs[] >>
     metis_tac[]) >>
  metis_tac[pop_nested_local_live_case]
QED
