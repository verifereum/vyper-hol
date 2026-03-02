(*
 * Lattice Standard Constructions — Correctness (Statements Only)
 *
 * Re-exports from proofs/latticeProofsScript.sml via ACCEPT_TAC.
 *)

Theory latticeProps
Ancestors
  latticeProofs

Theorem monotone_comp:
  !(leq : 'a -> 'a -> bool) f g.
    monotone leq f /\ monotone leq g ==>
    monotone leq (f o g)
Proof
  ACCEPT_TAC monotone_comp_proof
QED

Theorem inflationary_bounded_fixpoint:
  !(leq : 'a -> 'a -> bool) f (m : 'a -> num) b x.
    partial_order leq /\
    inflationary leq f /\
    bounded_measure leq m b ==>
    ?n. f (FUNPOW f n x) = FUNPOW f n x
Proof
  ACCEPT_TAC inflationary_bounded_fixpoint_proof
QED

Theorem bounded_measure_leq:
  !(leq : 'a -> 'a -> bool) (m : 'a -> num) b x y.
    bounded_measure leq m b /\ leq x y ==>
    m x <= m y
Proof
  ACCEPT_TAC bounded_measure_leq_proof
QED
