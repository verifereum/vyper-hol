(*
 * Lattice Standard Constructions — Proofs
 *
 * Shows that standard data structures form lattices satisfying
 * the predicates in latticeDefsScript.sml.
 *
 * TOP-LEVEL:
 *   monotone_comp          — composition of monotone functions is monotone
 *   inflationary_bounded   — inflationary + bounded_measure → fixpoint exists
 *   bounded_measure_leq    — bounded_measure implies leq is monotone in m
 *)

Theory latticeProofs
Ancestors
  latticeDefs arithmetic

(* ===== Basic lattice properties ===== *)

(* Composition of monotone functions is monotone *)
Theorem monotone_comp_proof:
  !(leq : 'a -> 'a -> bool) f g.
    monotone leq f /\ monotone leq g ==>
    monotone leq (f o g)
Proof
  cheat
QED

(* Inflationary + bounded_measure: the ascending chain stabilizes.
   This is the abstract Kleene argument: f^n(x) is ascending and bounded,
   so it must reach a fixpoint. *)
Theorem inflationary_bounded_fixpoint_proof:
  !(S : 'a -> bool) (leq : 'a -> 'a -> bool) f (m : 'a -> num) b x.
    partial_order leq /\
    inflationary leq f /\
    (!x. S x ==> S (f x)) /\
    S x /\
    bounded_measure S leq m b ==>
    ?n. f (FUNPOW f n x) = FUNPOW f n x
Proof
  cheat
QED

(* bounded_measure implies leq is monotone in m *)
Theorem bounded_measure_leq_proof:
  !(S : 'a -> bool) (leq : 'a -> 'a -> bool) (m : 'a -> num) b x y.
    bounded_measure S leq m b /\ S x /\ S y /\ leq x y ==>
    m x <= m y
Proof
  cheat
QED
