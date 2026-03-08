(*
 * Revert-to-Assert Pass — Correctness Statements
 *
 * Top-level correctness: the transformation preserves semantics
 * modulo fresh variables introduced by the pass.
 *
 * Proofs live in proofs/rtaCorrectnessProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory rtaCorrectness
Ancestors
  rtaCorrectnessProof

(* Revert-to-assert preserves execution semantics at the context level.
 * Given fresh_vars_not_in_context (original code doesn't use fresh names)
 * and an existing entry function, the transformed context contains a
 * corresponding function satisfying pass_correct: termination equivalence
 * and result equivalence modulo fresh variables.
 * Requires initial state with vs_inst_idx = 0 and not halted. *)
Theorem rta_pass_correct:
  !ctx entry.
    fresh_vars_not_in_context ctx /\
    no_invoke_in_context ctx /\
    lookup_function entry ctx.ctx_functions <> NONE
  ==>
    let ctx' = transform_context ctx in
    let fresh = fresh_vars_in_context ctx in
    ?fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' /\
      !s. s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
          pass_correct fresh
            (\fuel. run_function fuel ctx fn s)
            (\fuel. run_function fuel ctx fn' s)
Proof
  ACCEPT_TAC revert_to_assert_pass_correct
QED
