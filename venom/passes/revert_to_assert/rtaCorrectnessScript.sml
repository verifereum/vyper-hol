(*
 * Revert-to-Assert Pass — Correctness
 *
 * Top-level correctness: the transformation preserves semantics
 * modulo fresh variables introduced by the pass.
 *
 * Proof strategy: instantiate resolving_block_sim_function from the
 * cross-block simulation framework. RTA uses resolution n=1 for
 * JNZ-to-revert blocks (original jumps to revert block, transformed
 * reverts inline; one resolution step runs the revert block).
 *)

Theory rtaCorrectness
Ancestors
  rtaDefs rtaCorrectnessProofs venomWf
  crossBlockSimProps passSimulationProps
  stateEquiv stateEquivProps execEquivProps
  venomExecProps venomExecSemantics venomInst venomState

(* Revert-to-assert preserves execution semantics at the context level. *)
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
  ACCEPT_TAC rta_pass_correct_proof
QED

(* ===== Obligations ===== *)

Theorem rta_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (transform_function fn)
Proof
  cheat
QED

Theorem rta_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (transform_function fn)
Proof
  cheat
QED
