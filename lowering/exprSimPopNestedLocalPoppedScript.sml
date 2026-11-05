(*
 * Pop on a nested memory local: the one fact pop_nested_local_sim needs
 * that no invariant gives, admitted on its own (see the comment on it).
 *)

Theory exprSimPopNestedLocalPopped
Ancestors
  loweringPosts exprLoweringProps compileEnv vyperState valueEncoding

(* ADMITTED (popped history): a path that is dead in a local's value but
   read through its popped history sits in memory at its offset.

   This is how the target's place can come to a pop: in
   x[0][x.pop()[0][0]].pop(), with x : DynArray[DynArray[DynArray[uint256,
   2],2],2] of length 1, extend_place checks x[0] against x's live value,
   the index then pops x, and the last step reads x[0] from the history
   (read_memory_path),
   so the place x[0][i] is dead in x's value.  The lowering computed x[0]'s
   pointer before the index popped x and pops the array it finds there:
   the stale bytes of the popped element, which are the history's snapshot.

   No invariant says so: stmt_state_rel (local_ptrs_rel) relates only
   entry.value to memory, and popped_keys_indexed only types the history.
   Counterexample to the statement as it stands: x : DynArray[DynArray[
   uint256,2],2] with value ArrayV (DynArrayV []) and history
   [([ValueSubscript (IntV 0)], ArrayV (DynArrayV [IntV 5]))], memory all
   zero at x's region.  local_ptrs_rel holds (x's length word is 0), path
   [ValueSubscript (IntV 0)] is dead in the value and read_popped gives the
   snapshot, but the word at w + 32 is 0, not the snapshot's length 1.
   Proving it needs an invariant tying a local's popped history to the
   memory past its live data. *)
Theorem pop_local_popped_in_memory:
  !ctx func cenv cx es s id entry p sz w path k ptv err v.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    mem_path_offset entry.type path = SOME (k,ptv) /\
    evaluate_subscripts entry.type entry.value path = INR err /\
    read_popped entry.type path entry.popped = SOME v ==>
    val_in_memory ptv v (w2n w + k) s.vs_memory
Proof
  cheat
QED
