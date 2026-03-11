(*
 * Tail Merge Pass — Correctness Proof (cheated)
 *
 * Proves: merging structurally equivalent halting blocks preserves semantics.
 * Key insight: merged blocks have identical instruction sequences (modulo
 * α-renaming), so redirecting jumps to the keeper block produces the same
 * execution result.
 *)

Theory tailMergeProof
Ancestors
  tailMergeDefs stateEquiv venomExecSemantics

(* Tail merge preserves execution semantics at the function level.
 * Merged blocks are halting and self-contained, so variable names differ
 * (α-renamed) but all observable state (memory, storage, logs, returndata)
 * is identical. UNIV excludes all variable comparisons. *)
Theorem tail_merge_fn_correct:
  !func s fuel ctx.
    wf_function func ==>
    let func' = tail_merge_fn func in
    result_equiv UNIV
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  cheat
QED
