(*
 * Dataflow Iterate — Correctness (Statements Only)
 *
 * Convergence theorems for iterate-until-fixpoint.
 * Conditions: f has a bounded measure that strictly increases when f(x) ≠ x.
 *
 * Proofs live in proofs/dfIterateProofsScript.sml;
 * this file re-exports via ACCEPT_TAC.
 *)

Theory dfIterateProps
Ancestors
  dfIterateProofs

(* If f strictly increases a bounded measure when it changes something,
   then df_iterate returns a fixpoint. *)
Theorem df_iterate_fixpoint:
  !(f : 'a -> 'a) (m : 'a -> num) b x.
    (!y. f y <> y ==> m (f y) > m y) /\
    (!y. m y <= b) ==>
    f (df_iterate f x) = df_iterate f x
Proof
  ACCEPT_TAC df_iterate_fixpoint_proof
QED

(* Under the same conditions, df_iterate equals FUNPOW f n x for some n. *)
Theorem df_iterate_terminates:
  !(f : 'a -> 'a) (m : 'a -> num) b x.
    (!y. f y <> y ==> m (f y) > m y) /\
    (!y. m y <= b) ==>
    ?n. df_iterate f x = FUNPOW f n x
Proof
  ACCEPT_TAC df_iterate_terminates_proof
QED
