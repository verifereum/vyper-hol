(*
 * Dataflow Iterate — Definition
 *
 * General iterate-until-fixpoint via HOL4's WHILE combinator.
 * No analysis-specific dependencies.
 *
 * TOP-LEVEL:
 *   df_iterate — iterate f until fixpoint
 *
 * TODO: generalize to a full reusable dataflow framework:
 *   - Abstract lattice type with ⊑, ⊥, ⊔ (join)
 *   - Monotone transfer function predicate
 *   - Forward and backward analysis directions
 *   - Worklist-based iteration (not just round-robin)
 *   - Convergence for arbitrary finite lattices (Kleene/Tarski)
 *   - Widening/narrowing for infinite-height lattices
 *)

Theory dfIterateDefs
Ancestors
  While

Definition df_iterate_def:
  df_iterate f x = WHILE (\y. f y <> y) f x
End
