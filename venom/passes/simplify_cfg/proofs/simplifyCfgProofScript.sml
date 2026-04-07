(*
 * Simplify CFG Pass — Correctness Proof (cheated)
 *
 * Proves: block merging, trivial jump bypass, and unreachable block
 * removal preserve execution semantics.
 * Key insight: merged blocks execute the same instruction sequence;
 * bypassed trivial jumps are no-ops; unreachable blocks never execute.
 *)

Theory simplifyCfgProof
Ancestors
  simplifyCfgDefs stateEquiv venomExecSemantics

(* Simplify CFG preserves execution semantics at the function level.
 * Since block merging reduces block count, the transformed function
 * may need less fuel. We existentially quantify: for any fuel where
 * the original terminates, there exists sufficient fuel for the
 * transformed function to produce an equivalent result. *)
Theorem simplify_cfg_fn_correct:
  !func s fuel ctx.
    wf_function func ==>
    let func' = simplify_cfg_fn func in
    ?fuel'.
      result_equiv {}
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  cheat
QED
