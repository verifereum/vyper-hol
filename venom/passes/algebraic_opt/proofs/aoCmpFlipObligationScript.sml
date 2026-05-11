(* Obligation: cmp_flip preserves block execution up to dead variables.
 *
 * ao_cmp_flip_function is a mini-pass that flips comparators
 * (GT<->LT, SGT<->SLT) to eliminate trailing iszero instructions.
 * The flipped comparator output has a different value, but the
 * variable is "dead" — only used through the (now-removed) iszero.
 *
 * To prove this, the agent should:
 *   1. Compose existing step-level proofs from
 *      algebraicOptCmpFlipSimScript.sml (flip_step_exec_equiv,
 *      remove_step_exec_equiv) and algebraicOptCmpFlipBlockProofScript.sml
 *      into a block-level simulation by induction on the instruction list.
 *   2. Handle 4 instruction cases: unchanged (trivial), flipped
 *      (output dead), removed (iszero->assign), inserted (new iszero).
 *
 * Existing infrastructure:
 *   - Step-level flip pair equivalences in algebraicOptCmpFlipSimScript.sml
 *   - Block simulation framework in passSimulationProps
 *   - Partial block proof in algebraicOptCmpFlipBlockProofScript.sml
 *)
Theory aoCmpFlipObligation
Ancestors
  algebraicOptDefs stateEquiv execEquivProps venomExecSemantics

Theorem ao_cmp_flip_block_sim:
  !dfg fn1 lbl bb1 bb' fuel ctx s1 s2.
    let dead = ao_cmp_flip_dead_vars dfg fn1 in
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function dfg fn1).fn_blocks = SOME bb' /\
    state_equiv dead s1 s2 /\ s1.vs_inst_idx = 0 ==>
    lift_result (state_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb' s2)
Proof
  cheat
QED
