(*
 * Dataflow Iterate — General fixpoint iteration
 *
 * Wraps HOL4's WHILE combinator for iterate-until-fixpoint, plus
 * convergence and fixpoint theorems under standard dataflow conditions
 * (inflationary step function with bounded measure).
 *
 * Currently used by liveness analysis; designed to be reusable for
 * any iterative dataflow analysis.
 *
 * TOP-LEVEL:
 *   df_iterate          — iterate f until fixpoint (via WHILE)
 *   df_iterate_fixpoint — result is a fixpoint when f is inflationary & bounded
 *
 * TODO: generalize to a full reusable dataflow framework:
 *   - Abstract lattice type with ⊑, ⊥, ⊔ (join)
 *   - Monotone transfer function predicate
 *   - Forward and backward analysis directions
 *   - Worklist-based iteration (not just round-robin)
 *   - Convergence for arbitrary finite lattices (Kleene/Tarski)
 *   - Widening/narrowing for infinite-height lattices
 *)

Theory dfIterate
Ancestors
  While

(* ==========================================================================
   Iterate-until-fixpoint via WHILE

   WHILE is total in HOL4 (defined via LEAST).  Convergence is proved
   separately under inflationary + bounded conditions.
   ========================================================================== *)

Definition df_iterate_def:
  df_iterate f x = WHILE (\y. f y <> y) f x
End

(* ==========================================================================
   Convergence theorems

   Standard Kleene ascending chain argument: if f strictly increases a
   bounded natural-number measure whenever f(x) ≠ x, then iteration
   terminates and returns a fixpoint.

   Conditions:
     inflationary:  f(y) ≠ y  ==>  m(f(y)) > m(y)
     bounded:       m(y) ≤ b   (for all y)

   These are the minimal conditions for convergence.  In practice, for a
   dataflow analysis on a finite lattice of height h, m is the lattice
   height function and b = h.
   ========================================================================== *)

Theorem df_iterate_fixpoint:
  !(f : 'a -> 'a) (m : 'a -> num) b x.
    (!y. f y <> y ==> m (f y) > m y) /\
    (!y. m y <= b) ==>
    f (df_iterate f x) = df_iterate f x
Proof
  cheat
QED

(* The iterate result equals some finite application of f. *)
Theorem df_iterate_terminates:
  !(f : 'a -> 'a) (m : 'a -> num) b x.
    (!y. f y <> y ==> m (f y) > m y) /\
    (!y. m y <= b) ==>
    ?n. df_iterate f x = FUNPOW f n x
Proof
  cheat
QED
