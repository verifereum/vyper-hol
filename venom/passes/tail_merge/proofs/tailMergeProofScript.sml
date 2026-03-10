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
 * For any well-formed function, redirecting jumps from equivalent halting
 * blocks to a single keeper block and removing duplicates preserves the
 * execution result for any initial state. *)
Theorem tail_merge_fn_correct:
  !func s fuel ctx.
    wf_ir_fn func /\
    func.fn_blocks <> [] ==>
    let func' = tail_merge_fn func in
    result_equiv {}
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  cheat
QED
