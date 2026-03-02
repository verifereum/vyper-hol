(*
 * Lattice Predicates — Definitions
 *
 * Predicate-based lattice infrastructure for dataflow analysis.
 * Uses reflexive/transitive/antisymmetric from relationTheory.
 * No project-specific dependencies.
 *
 * TOP-LEVEL:
 *   partial_order   — reflexive, antisymmetric, transitive
 *   bounded_measure  — bounded + strictly monotone measure
 *   monotone         — order-preserving function
 *   inflationary     — f(x) ≥ x
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
