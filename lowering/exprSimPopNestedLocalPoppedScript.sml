(*
 * Pop on a nested memory local whose target reads a popped snapshot: the
 * residual case of pop_nested_local_sim, admitted on its own (see the
 * comment on it).
 *)

Theory exprSimPopNestedLocalPopped
Ancestors
  exprSimPopNestedBase
  loweringPosts exprSimDefs exprSimHypsDefs exprLoweringProps compileEnv
  vyperInterpreter vyperState valueEncoding

(* RESIDUAL (popped history): a target whose place, after its evaluation,
   is dead in the local's value and read from the local's popped history.

   The target's own index pops an ancestor of the popped array: in
   x[0][x.pop()[0][0]].pop(), with x : DynArray[DynArray[DynArray[uint256,
   2],2],2] of length 1, extend_place checks x[0] against x's live value,
   the index then pops x, and the last step reads x[0] from the history
   (read_memory_path), so the place x[0][i] is dead in x's value.  The
   lowering computed x[0]'s pointer before the index popped x and pops the
   array it finds there: the stale bytes of the popped element, which are
   the history's snapshot.

   The invariants lack this fact: stmt_state_rel's local_ptrs_rel relates
   only entry.value to memory, and popped_keys_indexed only types the
   history.  So nothing relates the snapshot the source pops to the bytes
   the lowering pops.  E.g. x : DynArray[DynArray[uint256,2],2] with value
   ArrayV (DynArrayV []) and history
   [([ValueSubscript (IntV 0)], ArrayV (DynArrayV [IntV 5]))], memory all
   zero at x's region: local_ptrs_rel holds (x's length word is 0), the
   source pops x[0] from the snapshot, and the lowering loads length 0 at
   x[0]'s pointer and aborts.  The fix is for local_ptrs_rel to also
   relate a local's popped history to memory. *)
Theorem pop_nested_local_popped_case:
  !ctx func cenv cx env ann bt ty es id s path t entry err v.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id /\
    eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
    lookup_scopes id t.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INR err /\
    read_popped entry.type path entry.popped = SOME v ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED
