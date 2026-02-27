(*
 * Liveness Analysis — Correctness Proofs
 *
 * Proof obligations:
 *  1. Fixpoint: liveness_analyze returns a fixpoint of the dataflow equations
 *     (one more pass doesn't change anything).
 *  2. Monotonicity: liveness_one_pass only adds variables to live sets.
 *  3. Boundedness: total_live_count ≤ all_var_slots.
 *  4. Soundness: every variable in a live set is used on some path
 *     before being redefined.
 *  5. PHI correctness: input_vars_from selects the right predecessor operand.
 *
 * (1) follows directly from the iterate-until-fixpoint structure.
 * (2)+(3) together give the termination argument.
 * (4) is the main semantic correctness theorem.
 *)

Theory livenessProofs
Ancestors
  livenessDefs cfgDefs
