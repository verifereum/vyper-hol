(* Function Inliner — Correctness Statement (re-exported) *)

Theory functionInlinerCorrectness
Ancestors
  functionInlinerProof

Theorem function_inliner_pass_correct:
  ∀ctx s fuel threshold.
    EVERY wf_function ctx.ctx_functions ∧
    EVERY alloca_pointer_confined ctx.ctx_functions ⇒
    let ctx' = function_inliner_ctx threshold ctx in
    ∃fuel'.
      result_equiv {}
        (run_context fuel ctx s)
        (run_context fuel' ctx' s)
Proof
  ACCEPT_TAC function_inliner_correct
QED

(* ===== Obligations ===== *)

(* Inliner preserves wf_function for all functions in context. *)
Theorem function_inliner_preserves_wf_function:
  ∀ctx threshold.
    EVERY wf_function ctx.ctx_functions ⇒
    EVERY wf_function (function_inliner_ctx threshold ctx).ctx_functions
Proof
  cheat
QED
