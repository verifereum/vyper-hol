(*
 * Lattice Standard Constructions — Properties
 *
 * Public algebraic facts about lattice definitions.
 *)

Theory latticeProps
Ancestors
  latticeDefs arithmetic

(* Composition of monotone functions is monotone. *)
Theorem monotone_comp:
  !(leq : 'a -> 'a -> bool) f g.
    monotone leq f /\ monotone leq g ==>
    monotone leq (f o g)
Proof
  rw[monotone_def]
QED

(* Inflationary f with bounded measure on domain S reaches a fixpoint
   from any starting point in S. Requires partial_order and S closed under f. *)
Theorem inflationary_bounded_fixpoint:
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

(* Bounded measure is weakly monotone within domain S: leq x y implies m x ≤ m y. *)
Theorem bounded_measure_leq:
  !(S : 'a -> bool) (leq : 'a -> 'a -> bool) (m : 'a -> num) b x y.
    bounded_measure S leq m b /\ S x /\ S y /\ leq x y ==>
    m x <= m y
Proof
  rw[bounded_measure_def] >>
  Cases_on `x = y` >> res_tac >> fs[]
QED
