(*
 * Dataflow Shared Helpers — Definitions
 *
 * Thin wrappers over HOL4 stdlib used by multiple analyses
 * (dominators, var_def, available_expr).
 *
 * No project-specific dependencies.
 *
 * TOP-LEVEL:
 *   list_intersect      — FILTER + MEM intersection
 *   list_intersect_all  — iterated intersection
 *   fmap_lookup_default — FLOOKUP with fallback
 *
 * NOT defined here (use stdlib directly):
 *   fmap domain intersection → DRESTRICT f (FDOM g)
 *   list union → already in livenessDefsScript (or use nub (xs ++ ys))
 *)

Theory dfHelperDefs
Ancestors
  list finite_map

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

(* FLOOKUP with default value *)
Definition fmap_lookup_default_def:
  fmap_lookup_default d f k =
    case FLOOKUP f k of SOME v => v | NONE => d
End
