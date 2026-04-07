(* Function Inliner — Correctness Statement (re-exported) *)

Theory functionInlinerCorrectness
Ancestors
  functionInlinerProof

open functionInlinerProofTheory

Theorem function_inliner_pass_correct:
  !ctx s fuel threshold.
    inliner_ctx_wf ctx <| is_inline_count := 0; is_label_counter := 0 |> /\
    FDOM s.vs_labels = {} /\
    ~s.vs_halted ==>
    let ctx' = function_inliner_ctx threshold ctx in
    ?fuel'.
      inliner_result_equiv inline_vars
        (run_context fuel ctx s)
        (run_context fuel' ctx' s)
Proof
  ACCEPT_TAC function_inliner_correct
QED

val _ = export_theory();
