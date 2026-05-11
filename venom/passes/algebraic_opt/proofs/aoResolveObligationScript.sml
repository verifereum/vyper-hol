(* Obligation: iszero resolution preserves step_inst semantics.
 *
 * ao_resolve_iszero_inst replaces operands that are at the end of an
 * iszero chain with earlier chain elements (e.g. iz(iz(x)) -> x in
 * truthy contexts).  This is correct because iszero chains collapse
 * with period 2, and in the actual execution state the chain variables
 * have the right iszero relationships.
 *
 * NOTE: The current formulation (forall s) is TOO STRONG.  Resolution
 * changes operands, so the result differs in arbitrary states.  It is
 * only correct when the iszero chain invariant holds in s — i.e., the
 * chain variables satisfy their iszero relationships.
 *
 * To prove this, the agent should:
 *   1. Define ao_iszero_chain_inv targets s
 *   2. Prove the chain invariant is maintained during block execution
 *   3. Prove that under the invariant, resolution is a no-op on step_inst
 *   4. Integrate the invariant into the block simulation's sinv
 *      (in algebraicOptProofsScript.sml, alongside ao_dfg_inv)
 *
 * The reformulation will require changes to ao_transform_inst_sim_inst
 * and ao_per_inst_sim_fn0 in algebraicOptProofsScript.sml to thread
 * the chain invariant through the block simulation.
 *)
Theory aoResolveObligation
Ancestors
  algebraicOptDefs venomExecSemantics venomWf

Theorem ao_resolve_iszero_inst_sim:
  !targets inst fuel ctx s.
    inst_wf inst ==>
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
    step_inst fuel ctx inst s
Proof
  cheat
QED
