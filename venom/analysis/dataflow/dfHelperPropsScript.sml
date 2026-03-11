(*
 * Dataflow Shared Helpers — Properties (Statements Only)
 *
 * Re-exports from proofs/dfHelperProofsScript.sml via ACCEPT_TAC.
 *
 * TOP-LEVEL:
 *   list_intersect_set          — set (list_intersect xs ys) = set xs ∩ set ys
 *   list_intersect_mem          — MEM characterization
 *   list_intersect_all_set      — set result = BIGINTER ...
 *   list_intersect_all_mono     — result ⊆ first element
 *   list_intersect_all_distinct — preserves ALL_DISTINCT
 *   list_intersect_absorption   — intersect(intersect(a,b),b) = intersect(a,b)
 *   list_intersect_length_le    — LENGTH result ≤ LENGTH first arg
 *   all_distinct_psubset_length — ALL_DISTINCT + strict subset ⇒ LENGTH <
 *   sum_map_bounded             — SUM(MAP f ls) ≤ c * LENGTH ls when each f x ≤ c
 *   foldl_list_intersect_acc_mono — acc monotone: set a ⊆ set b ⇒ FOLDL ⊆ FOLDL
 *   foldl_list_intersect_mono  — element-wise monotone: pointwise ⊆ ⇒ FOLDL ⊆ FOLDL
 *   list_union_mem              — MEM characterization
 *   list_union_set              — set (list_union xs ys) = set xs ∪ set ys
 *)

Theory dfHelperProps
Ancestors
  dfHelperProofs

(* Set of list_intersect is the set intersection. *)
Theorem list_intersect_set:
  !xs ys. set (list_intersect xs ys) = set xs INTER set ys
Proof
  ACCEPT_TAC list_intersect_set_proof
QED

(* Membership in list_intersect iff member of both lists. *)
Theorem list_intersect_mem:
  !v xs ys. MEM v (list_intersect xs ys) <=> MEM v xs /\ MEM v ys
Proof
  ACCEPT_TAC list_intersect_mem_proof
QED

(* For nonempty input, iterated intersection equals BIGINTER of the sets. *)
Theorem list_intersect_all_set:
  !ls. ls <> [] ==>
    set (list_intersect_all ls) = BIGINTER (IMAGE set (set ls))
Proof
  ACCEPT_TAC list_intersect_all_set_proof
QED

(* Iterated intersection is a subset of the first list. *)
Theorem list_intersect_all_mono:
  !l ls. set (list_intersect_all (l :: ls)) SUBSET set l
Proof
  ACCEPT_TAC list_intersect_all_mono_proof
QED

(* list_intersect preserves ALL_DISTINCT. *)
Theorem list_intersect_all_distinct:
  !xs ys. ALL_DISTINCT xs ==> ALL_DISTINCT (list_intersect xs ys)
Proof
  ACCEPT_TAC list_intersect_all_distinct_proof
QED

(* list_intersect absorption: intersect(intersect(a,b), b) = intersect(a,b). *)
Theorem list_intersect_absorption:
  !a b. list_intersect (list_intersect a b) b = list_intersect a b
Proof
  ACCEPT_TAC list_intersect_absorption_proof
QED

(* ALL_DISTINCT + strict subset implies LENGTH strictly less. *)
Theorem all_distinct_psubset_length:
  !xs ys.
    ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
    set xs SUBSET set ys /\ set xs <> set ys ==>
    LENGTH xs < LENGTH ys
Proof
  ACCEPT_TAC all_distinct_psubset_length_proof
QED

(* list_intersect length bounded by first argument. *)
Theorem list_intersect_length_le:
  !xs ys. LENGTH (list_intersect xs ys) <= LENGTH xs
Proof
  ACCEPT_TAC list_intersect_length_le_proof
QED

(* SUM of bounded values is bounded by constant * length. *)
Theorem sum_map_bounded:
  !f ls c. EVERY (\x. f x <= c) ls ==> SUM (MAP f ls) <= c * LENGTH ls
Proof
  ACCEPT_TAC sum_map_bounded_proof
QED

(* SUM monotone: pointwise ≤ implies SUM ≤. *)
Theorem sum_map_mono:
  !f g ls. EVERY (\x. f x <= g x) ls ==>
    SUM (MAP f ls) <= SUM (MAP g ls)
Proof
  ACCEPT_TAC sum_map_mono_proof
QED

(* SUM strictly increases when one element strictly increases and rest ≤. *)
Theorem sum_map_strict_increase:
  !f g x xs. MEM x xs /\ f x < g x /\ EVERY (\y. f y <= g y) xs ==>
    SUM (MAP f xs) < SUM (MAP g xs)
Proof
  ACCEPT_TAC sum_map_strict_increase_proof
QED

(* FOLDL list_intersect: result is subset of initial accumulator. *)
Theorem foldl_list_intersect_subset:
  !xs a. set (FOLDL list_intersect a xs) SUBSET set a
Proof
  ACCEPT_TAC foldl_list_intersect_subset_proof
QED

(* FOLDL list_intersect: accumulator monotonicity. *)
Theorem foldl_list_intersect_acc_mono:
  !xs a b. set a SUBSET set b ==>
    set (FOLDL list_intersect a xs) SUBSET set (FOLDL list_intersect b xs)
Proof
  ACCEPT_TAC foldl_list_intersect_acc_mono_proof
QED

(* FOLDL list_intersect: element-wise monotonicity. *)
Theorem foldl_list_intersect_mono:
  !xs ys a. LENGTH xs = LENGTH ys /\
    (!i. i < LENGTH xs ==> set (EL i xs) SUBSET set (EL i ys)) ==>
    set (FOLDL list_intersect a xs) SUBSET set (FOLDL list_intersect a ys)
Proof
  ACCEPT_TAC foldl_list_intersect_mono_proof
QED

(* list_intersect strict length decrease when result differs from input. *)
Theorem list_intersect_strict_length:
  !a b. ALL_DISTINCT a /\ list_intersect a b <> a ==>
    LENGTH (list_intersect a b) < LENGTH a
Proof
  ACCEPT_TAC list_intersect_strict_length_proof
QED

(* FOLDL list_intersect preserves ALL_DISTINCT. *)
Theorem foldl_intersect_all_distinct:
  !xs base. ALL_DISTINCT base ==>
    ALL_DISTINCT (FOLDL list_intersect base xs)
Proof
  ACCEPT_TAC foldl_intersect_all_distinct_proof
QED

(* FOLDL list_intersect base xs is always a FILTER of base. *)
Theorem foldl_intersect_is_filter:
  !xs base. ?P. FOLDL list_intersect base xs = FILTER P base
Proof
  ACCEPT_TAC foldl_intersect_is_filter_proof
QED

(* Two FILTERs of an ALL_DISTINCT list with equal sets are equal. *)
Theorem filter_set_eq_filter_eq:
  !P Q base. ALL_DISTINCT base ==>
    set (FILTER P base) = set (FILTER Q base) ==>
    FILTER P base = FILTER Q base
Proof
  ACCEPT_TAC filter_set_eq_filter_eq_proof
QED

(* Membership in list_union iff member of either list. *)
Theorem list_union_mem:
  !v xs ys. MEM v (list_union xs ys) <=> MEM v xs \/ MEM v ys
Proof
  ACCEPT_TAC list_union_mem_proof
QED

(* Set of list_union is the set union. *)
Theorem list_union_set:
  !xs ys. set (list_union xs ys) = set xs UNION set ys
Proof
  ACCEPT_TAC list_union_set_proof
QED
