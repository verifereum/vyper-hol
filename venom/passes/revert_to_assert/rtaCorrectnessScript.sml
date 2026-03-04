(*
 * Revert-to-Assert Pass — Correctness Statements
 *
 * Top-level correctness: the transformation preserves semantics
 * modulo fresh variables introduced by the pass.
 * Uses pass_correct which establishes termination equivalence and
 * result equivalence (modulo fresh variables).
 *
 * Proofs live in proofs/rtaCorrectnessScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory rtaCorrectness
Ancestors
  rtaCorrectnessProof

(* Revert-to-assert preserves execution semantics at the context level.
 * For any entry function, the original and transformed contexts
 * produce equivalent results (modulo fresh variables). *)
Theorem rta_pass_correct:
  !ctx entry.
    fresh_vars_not_in_context ctx /\
    lookup_function entry ctx.ctx_functions <> NONE
  ==>
    let ctx' = transform_context ctx in
    let fresh = fresh_vars_in_context ctx in
    ?fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' /\
      !s. s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
          pass_correct fresh
            (\fuel. run_function fuel fn s)
            (\fuel. run_function fuel fn' s)
Proof
  ACCEPT_TAC revert_to_assert_pass_correct
QED
