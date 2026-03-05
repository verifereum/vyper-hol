(*
 * Dataflow Shared Helpers — Definitions
 *
 * Thin wrappers over HOL4 stdlib used by multiple analyses
 * (dominators, available_expr, liveness, var_definition).
 *
 * No project-specific dependencies.
 *
 * TOP-LEVEL:
 *   list_intersect      — FILTER + MEM intersection
 *   list_intersect_all  — iterated intersection
 *   list_union          — xs ++ (ys \ xs), list-backed set union
 *)

Theory dfHelperDefs
Ancestors
  list

(* List intersection: elements of xs that also appear in ys *)
Definition list_intersect_def:
  list_intersect xs ys = FILTER (λx. MEM x ys) xs
End

(* Iterated list intersection.
   Empty input → [] (no universal element).
   Singleton → identity.
   Otherwise fold pairwise. *)
Definition list_intersect_all_def:
  list_intersect_all [] = [] ∧
  list_intersect_all [xs] = xs ∧
  list_intersect_all (xs :: rest) =
    list_intersect xs (list_intersect_all rest)
End

(* List union: xs ∪ ys as list (no dups if xs has no dups). *)
Definition list_union_def:
  list_union xs ys = xs ++ FILTER (λv. ¬MEM v xs) ys
End
