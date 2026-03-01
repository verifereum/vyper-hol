(*
 * Lattice Predicates — Definitions
 *
 * Predicate-based lattice infrastructure for dataflow analysis.
 * No project-specific dependencies.
 *
 * TOP-LEVEL:
 *   partial_order   — reflexive, antisymmetric, transitive
 *   bounded_measure  — bounded + strictly monotone measure
 *   monotone         — order-preserving function
 *   inflationary     — f(x) ≥ x
 *)

Theory latticeDefs

(* Partial order: reflexive, antisymmetric, transitive *)
Definition partial_order_def:
  partial_order (leq : 'a -> 'a -> bool) <=>
    (!x. leq x x) /\
    (!x y. leq x y /\ leq y x ==> (x = y)) /\
    (!x y z. leq x y /\ leq y z ==> leq x z)
End

(* Bounded measure witnessing finite height:
   m is bounded above by b and strictly reflects the order *)
Definition bounded_measure_def:
  bounded_measure (leq : 'a -> 'a -> bool) (m : 'a -> num) (b : num) <=>
    (!x. m x <= b) /\
    (!x y. leq x y /\ x <> y ==> m x < m y)
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
