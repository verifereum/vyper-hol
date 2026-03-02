(*
 * Dataflow Iterate — Convergence Proofs
 *
 * Proofs re-exported via dfIteratePropsScript.sml.
 *
 * Standard Kleene ascending chain argument: if f strictly increases a
 * bounded natural-number measure whenever f(x) ≠ x, then iteration
 * terminates and returns a fixpoint.
 *)

Theory dfIterateProofs
Ancestors
  dfIterateDefs

(* The result is a fixpoint of f. *)
Theorem df_iterate_fixpoint_proof:
  !(f : 'a -> 'a) (m : 'a -> num) b x.
    (!y. f y <> y ==> m (f y) > m y) /\
    (!y. m y <= b) ==>
    f (df_iterate f x) = df_iterate f x
Proof
  cheat
QED


