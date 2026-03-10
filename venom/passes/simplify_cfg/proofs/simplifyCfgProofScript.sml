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

(* Simplify CFG preserves execution semantics at the function level. *)
Theorem simplify_cfg_fn_correct:
  !func s fuel ctx.
    wf_ir_fn func /\
    func.fn_blocks <> [] ==>
    let func' = simplify_cfg_fn func in
    result_equiv {}
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  cheat
QED
