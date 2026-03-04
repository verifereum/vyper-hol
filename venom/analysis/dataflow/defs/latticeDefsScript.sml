(*
 * Lattice Predicates — Definitions
 *
 * Predicate-based lattice infrastructure for dataflow analysis.
 * Uses reflexive/transitive/antisymmetric from relationTheory.
 * No project-specific dependencies.
 *
 * TOP-LEVEL:
 *   partial_order    — reflexive, antisymmetric, transitive
 *   bounded_measure  — bounded + strictly monotone measure
 *   monotone         — order-preserving function
 *   inflationary     — f(x) ≥ x
 *   widen_operator   — widening for infinite-height lattices
 *)

Theory latticeDefs
Ancestors
  relation

(* Partial order: reflexive, antisymmetric, transitive.
   Uses existing definitions from relationTheory. *)
Definition partial_order_def:
  partial_order (leq : 'a -> 'a -> bool) <=>
    reflexive leq /\ antisymmetric leq /\ transitive leq
End

(* Bounded measure witnessing finite height:
   m is bounded above by b and strictly reflects the order,
   within domain S *)
Definition bounded_measure_def:
  bounded_measure (S : 'a -> bool) (leq : 'a -> 'a -> bool)
                  (m : 'a -> num) (b : num) <=>
    (!x. S x ==> m x <= b) /\
    (!x y. S x /\ S y /\ leq x y /\ x <> y ==> m x < m y)
End

(* Monotone function: order-preserving *)
Definition monotone_def:
  monotone (leq : 'a -> 'a -> bool) (f : 'a -> 'a) <=>
    !x y. leq x y ==> leq (f x) (f y)
End

(* Inflationary function: f(x) ≥ x *)
Definition inflationary_def:
  inflationary (leq : 'a -> 'a -> bool) (f : 'a -> 'a) <=>
    !x. leq x (f x)
End

(* Widening operator for infinite-height lattices.
   widen x y produces an upper bound of both x and y,
   with bounded height: a measure exists that strictly increases
   when widening changes the value, so any widened chain stabilizes.
   h is the height bound (max number of widening steps per element). *)
Definition widen_operator_def:
  widen_operator (leq : 'a -> 'a -> bool) (widen : 'a -> 'a -> 'a) (h : num) <=>
    (!x y. leq x (widen x y)) /\
    (!x y. leq y (widen x y)) /\
    ?m. (!x. m x <= h) /\
        (!x y. widen x y <> x ==> m x < m (widen x y))
End
