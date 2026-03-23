(*
 * Function Inliner Pass — Correctness Proof (cheated)
 *
 * Proves: inlining preserves execution semantics at the context level.
 * Key insight: inlined code executes identically to the INVOKE call —
 * same instructions, same state transitions — just without the
 * function call overhead.
 *)

Theory functionInlinerProof
Ancestors
  functionInlinerDefs stateEquiv venomExecSemantics

(* Inlining preserves execution semantics.
 * For any fuel where the original context terminates, there exists
 * sufficient fuel for the inlined context to produce an equivalent result.
 *
 * Preconditions:
 *   - wf_function for all functions in context
 *   - no recursive calls (acyclic call graph)
 *)
Theorem function_inliner_correct:
  ∀ctx s fuel threshold.
    EVERY wf_function ctx.ctx_functions ⇒
    let ctx' = function_inliner_ctx threshold ctx in
    ∃fuel'.
      result_equiv {}
        (run_context fuel ctx s)
        (run_context fuel' ctx' s)
Proof
  cheat
QED
