(* Function Inliner — Correctness Statement (re-exported) *)

Theory functionInlinerCorrectness
Ancestors
  functionInlinerProof

Theorem function_inliner_pass_correct:
  ∀ctx s fuel threshold.
    EVERY wf_function ctx.ctx_functions ⇒
    let ctx' = function_inliner_ctx threshold ctx in
    ∃fuel'.
      result_equiv {}
        (run_context fuel ctx s)
        (run_context fuel' ctx' s)
Proof
  ACCEPT_TAC function_inliner_correct
QED
