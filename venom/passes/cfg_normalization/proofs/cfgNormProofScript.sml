(*
 * CFG Normalization Pass — Correctness Proof (cheated)
 *
 * Proves: inserting forwarding split blocks between conditional
 * predecessors and multi-predecessor targets preserves semantics.
 * Key insight: a split block S with forwarding assigns + JMP to B
 * produces the same state as jumping directly from P to B, because
 * the forwarding assigns copy exactly the values that the PHI would
 * select from P.
 *)

Theory cfgNormProof
Ancestors
  cfgNormDefs stateEquiv venomExecSemantics

(* CFG normalization preserves execution semantics at the function level. *)
Theorem cfg_norm_fn_correct:
  !func s fuel ctx.
    wf_ir_fn func /\
    func.fn_blocks <> [] ==>
    let func' = cfg_norm_fn func in
    result_equiv {}
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  cheat
QED
