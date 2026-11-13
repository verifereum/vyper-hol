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

Theorem sum_complement_mono:
  !f g (n:num) ls.
    (!x. MEM x ls ==> g x <= f x /\ f x <= n) ==>
    SUM (MAP (\x. n - f x) ls) <= SUM (MAP (\x. n - g x) ls)
Proof
  Induct_on `ls` >> simp[] >> rpt strip_tac >>
  `g h <= f h /\ f h <= n` by metis_tac[] >>
  `!x. MEM x ls ==> g x <= f x /\ f x <= n` by metis_tac[] >>
  res_tac >> DECIDE_TAC
QED

Theorem sum_complement_strict:
  !f g (n:num) ls x.
    MEM x ls /\ g x < f x /\ f x <= n /\
    (!y. MEM y ls ==> g y <= f y /\ f y <= n) ==>
    SUM (MAP (\y. n - f y) ls) < SUM (MAP (\y. n - g y) ls)
Proof
  Induct_on `ls` >> rw[] >> fs[] >> (
    `g h <= f h /\ f h <= n` by metis_tac[] >>
    `!y. MEM y ls ==> g y <= f y /\ f y <= n` by metis_tac[]
  )
  >- (`SUM (MAP (\y. n - f y) ls) <= SUM (MAP (\y. n - g y) ls)` by
        (irule sum_complement_mono >> metis_tac[]) >>
      DECIDE_TAC)
  >> `SUM (MAP (\y. n - f y) ls) < SUM (MAP (\y. n - g y) ls)` by
       (first_x_assum (qspecl_then [`f`, `g`, `n`, `x`] mp_tac) >> simp[] >>
        metis_tac[]) >>
     DECIDE_TAC
QED
