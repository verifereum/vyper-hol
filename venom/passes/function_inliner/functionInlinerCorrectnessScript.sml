(* Function inliner well-formedness *)

Theory functionInlinerCorrectness
Ancestors
  functionInlinerWf

(* Inliner preserves wf_function for all functions in context.
   Cloned blocks are named inl<n>_<label> and return blocks
   inl<n>_inline_return<c>, without checking the caller's labels (as in
   Python). Input labels must therefore not start with "inl": lowering's
   labels start with "@", function entries with "internal " or "__entry". *)
Theorem function_inliner_preserves_wf_function:
  ∀ctx threshold.
    EVERY wf_function ctx.ctx_functions ∧
    EVERY (λfunc. EVERY (λbb. ¬isPREFIX "inl" bb.bb_label) func.fn_blocks)
      ctx.ctx_functions ⇒
    EVERY wf_function (function_inliner_ctx threshold ctx).ctx_functions
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [functionInlinerDefsTheory.function_inliner_ctx_def, LET_THM] >>
  irule function_inliner_loop_wf >> gvs[]
QED
