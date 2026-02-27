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

(* Inflationary variant: if f grows a partial order and that order
   strictly increases a bounded measure, then df_iterate returns a fixpoint. *)
Theorem df_iterate_inflationary_fixpoint:
  !(f : 'a -> 'a) (leq : 'a -> 'a -> bool) (m : 'a -> num) b
   (P : 'a -> bool) x.
    (!y. P y ==> leq y (f y)) /\
    (!y z. leq y z /\ y <> z ==> m y < m z) /\
    P x /\
    (!y. P y ==> m y <= b) /\
    (!y. P y ==> P (f y)) ==>
    f (df_iterate f x) = df_iterate f x
Proof
  ACCEPT_TAC df_iterate_inflationary_fixpoint_proof
QED

(* Inflationary variant: the invariant P is preserved through iteration. *)
Theorem df_iterate_inflationary_invariant:
  !(f : 'a -> 'a) (leq : 'a -> 'a -> bool) (m : 'a -> num) b
   (P : 'a -> bool) x.
    (!y. P y ==> leq y (f y)) /\
    (!y z. leq y z /\ y <> z ==> m y < m z) /\
    P x /\
    (!y. P y ==> m y <= b) /\
    (!y. P y ==> P (f y)) ==>
    P (df_iterate f x)
Proof
  ACCEPT_TAC df_iterate_inflationary_invariant_proof
QED

