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
  rw[monotone_def]
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
  rw[]
  >> `!k. S' (FUNPOW f k x)` by (Induct >> fs[FUNPOW_SUC])
  >> completeInduct_on `b - m x`
  >> rw[]
  >> Cases_on `f x = x`
  >- (qexists_tac `0` >> fs[])
  >> `leq x (f x)` by fs[inflationary_def]
  >> `S' (f x)` by fs[]
  >> `m x < m (f x)` by fs[bounded_measure_def]
  >> `m (f x) <= b` by fs[bounded_measure_def]
  >> `b - m (f x) < b - m x` by fs[]
  >> qpat_x_assum `!m'. m' < _ ==> _`
       (qspec_then `b - m (f x)` mp_tac)
  >> impl_tac >- fs[]
  >> disch_then (qspecl_then [`b`, `m`, `f x`] mp_tac)
  >> impl_tac
  >- (rw[FUNPOW_SUC]
      >> first_x_assum (qspec_then `SUC k` mp_tac) >> fs[FUNPOW_SUC])
  >> impl_tac >- fs[]
  >> impl_tac >- fs[]
  >> impl_tac
  >- (rw[] >> qpat_x_assum `!k. S' (FUNPOW f k x)`
        (qspec_then `SUC k` mp_tac) >> simp[FUNPOW])
  >> rw[] >> qexists_tac `SUC n` >> fs[FUNPOW]
QED

(* bounded_measure implies leq is monotone in m *)
Theorem bounded_measure_leq_proof:
  !(S : 'a -> bool) (leq : 'a -> 'a -> bool) (m : 'a -> num) b x y.
    bounded_measure S leq m b /\ S x /\ S y /\ leq x y ==>
    m x <= m y
Proof
  rw[bounded_measure_def] >>
  Cases_on `x = y` >> res_tac >> fs[]
QED
