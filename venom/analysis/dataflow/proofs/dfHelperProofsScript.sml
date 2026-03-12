(*
 * Dataflow Shared Helpers — Proofs
 *)

Theory dfHelperProofs
Ancestors
  dfHelperDefs pred_set list

Theorem list_intersect_mem_proof:
  !v xs ys. MEM v (list_intersect xs ys) <=> MEM v xs /\ MEM v ys
Proof
  rw[list_intersect_def, MEM_FILTER] >> metis_tac[]
QED

Theorem list_intersect_set_proof:
  !xs ys. set (list_intersect xs ys) = set xs INTER set ys
Proof
  rw[EXTENSION, IN_INTER] >> metis_tac[list_intersect_mem_proof]
QED

Theorem list_intersect_all_set_proof:
  !ls. ls <> [] ==>
    set (list_intersect_all ls) = BIGINTER (IMAGE set (set ls))
Proof
  Induct >- rw[] >>
  rw[] >> Cases_on `ls` >>
  fs[list_intersect_all_def, list_intersect_set_proof]
QED

Theorem list_intersect_all_mono_proof:
  !l ls. set (list_intersect_all (l :: ls)) SUBSET set l
Proof
  rw[SUBSET_DEF] >>
  Cases_on `ls` >>
  fs[list_intersect_all_def, list_intersect_mem_proof]
QED

(* list_intersect preserves ALL_DISTINCT *)
Theorem list_intersect_all_distinct_proof:
  !xs ys. ALL_DISTINCT xs ==> ALL_DISTINCT (list_intersect xs ys)
Proof
  rw[list_intersect_def, FILTER_ALL_DISTINCT]
QED

(* list_intersect absorption: intersect(intersect(a,b), b) = intersect(a,b) *)
Theorem list_intersect_absorption_proof:
  !a b. list_intersect (list_intersect a b) b = list_intersect a b
Proof
  rw[list_intersect_def, rich_listTheory.FILTER_FILTER] >>
  AP_THM_TAC >> AP_TERM_TAC >> rw[FUN_EQ_THM, MEM_FILTER]
QED

(* ALL_DISTINCT + strict subset implies LENGTH strictly less *)
Theorem all_distinct_psubset_length_proof:
  !xs ys.
    ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
    set xs SUBSET set ys /\ set xs <> set ys ==>
    LENGTH xs < LENGTH ys
Proof
  rw[] >>
  `FINITE (set ys)` by rw[FINITE_LIST_TO_SET] >>
  `CARD (set xs) = LENGTH xs` by metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `CARD (set ys) = LENGTH ys` by metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `set xs PSUBSET set ys` by (rw[PSUBSET_DEF] >> metis_tac[]) >>
  `CARD (set xs) < CARD (set ys)` by metis_tac[CARD_PSUBSET] >>
  DECIDE_TAC
QED

(* list_intersect length bounded by first argument *)
Theorem list_intersect_length_le_proof:
  !xs ys. LENGTH (list_intersect xs ys) <= LENGTH xs
Proof
  rw[list_intersect_def, rich_listTheory.LENGTH_FILTER_LEQ]
QED

(* SUM of bounded values is bounded by constant * length *)
Theorem sum_map_bounded_proof:
  !f ls c. EVERY (\x. f x <= c) ls ==> SUM (MAP f ls) <= c * LENGTH ls
Proof
  gen_tac >> Induct >> rw[] >>
  `SUM (MAP f ls) <= c * LENGTH ls` by fs[] >>
  `f h <= c` by fs[] >>
  rw[arithmeticTheory.MULT_SUC] >> DECIDE_TAC
QED

(* SUM monotone: pointwise ≤ implies SUM ≤ *)
Theorem sum_map_mono_proof:
  !f g ls. EVERY (\x. f x <= g x) ls ==>
    SUM (MAP f ls) <= SUM (MAP g ls)
Proof
  gen_tac >> gen_tac >> Induct >> rw[] >>
  `SUM (MAP f ls) <= SUM (MAP g ls)` by fs[] >>
  `f h <= g h` by fs[] >>
  DECIDE_TAC
QED

(* SUM strictly increases when one element strictly increases and rest ≤ *)
Theorem sum_map_strict_increase_proof:
  !f g x xs. MEM x xs /\ f x < g x /\ EVERY (\y. f y <= g y) xs ==>
    SUM (MAP f xs) < SUM (MAP g xs)
Proof
  ntac 3 gen_tac >> Induct >> rw[]
  (* x = h case: f h < g h, use sum_map_mono on tail *)
  >- (`SUM (MAP f xs) <= SUM (MAP g xs)` suffices_by DECIDE_TAC >>
      irule sum_map_mono_proof >> fs[])
  (* x in tail case: IH gives strict on tail, f h <= g h *)
  >- (`SUM (MAP f xs) < SUM (MAP g xs)` suffices_by DECIDE_TAC >>
      first_x_assum irule >> rw[])
QED

(* list_intersect strict length decrease *)
Theorem list_intersect_strict_length_proof:
  !a b. ALL_DISTINCT a /\ list_intersect a b <> a ==>
    LENGTH (list_intersect a b) < LENGTH a
Proof
  rw[list_intersect_def] >>
  `ALL_DISTINCT (FILTER (\x. MEM x b) a)` by
    rw[FILTER_ALL_DISTINCT] >>
  `set (FILTER (\x. MEM x b) a) SUBSET set a` by
    rw[SUBSET_DEF, MEM_FILTER] >>
  `set (FILTER (\x. MEM x b) a) <> set a` by
    (CCONTR_TAC >> fs[EXTENSION, MEM_FILTER] >>
     `EVERY (\x. MEM x b) a` by (rw[EVERY_MEM] >> metis_tac[]) >>
     fs[GSYM FILTER_EQ_ID]) >>
  metis_tac[all_distinct_psubset_length_proof]
QED

(* FOLDL list_intersect: result is subset of initial accumulator *)
Theorem foldl_list_intersect_subset_proof:
  !xs a. set (FOLDL list_intersect a xs) SUBSET set a
Proof
  Induct >> rw[] >>
  irule SUBSET_TRANS >>
  qexists_tac `set (list_intersect a h)` >>
  rw[list_intersect_set_proof, INTER_SUBSET]
QED

(* FOLDL list_intersect: accumulator monotonicity *)
Theorem foldl_list_intersect_acc_mono_proof:
  !xs a b. set a SUBSET set b ==>
    set (FOLDL list_intersect a xs) SUBSET set (FOLDL list_intersect b xs)
Proof
  Induct >> rw[] >> first_x_assum irule >>
  rw[list_intersect_set_proof] >>
  fs[SUBSET_DEF, IN_INTER] >> metis_tac[]
QED

(* FOLDL list_intersect: element-wise monotonicity *)
Theorem foldl_list_intersect_mono_proof:
  !xs ys a. LENGTH xs = LENGTH ys /\
    (!i. i < LENGTH xs ==> set (EL i xs) SUBSET set (EL i ys)) ==>
    set (FOLDL list_intersect a xs) SUBSET set (FOLDL list_intersect a ys)
Proof
  Induct >> rw[] >> Cases_on `ys` >> fs[] >>
  irule SUBSET_TRANS >>
  qexists_tac `set (FOLDL list_intersect (list_intersect a h) t)` >>
  conj_tac
  >- (first_x_assum irule >> rw[] >>
      first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
  >- (irule foldl_list_intersect_acc_mono_proof >>
      rw[list_intersect_set_proof, SUBSET_DEF, IN_INTER] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
      fs[SUBSET_DEF])
QED

(* FOLDL list_intersect preserves ALL_DISTINCT *)
Theorem foldl_intersect_all_distinct_proof:
  !xs bse. ALL_DISTINCT bse ==>
    ALL_DISTINCT (FOLDL list_intersect bse xs)
Proof
  Induct >> rw[FOLDL] >>
  first_x_assum irule >>
  rw[list_intersect_def, FILTER_ALL_DISTINCT]
QED

(* FOLDL list_intersect bse xs is always a FILTER of bse *)
Theorem foldl_intersect_is_filter_proof:
  !xs bse. ?P. FOLDL list_intersect bse xs = FILTER P bse
Proof
  Induct >> rw[]
  >- (qexists_tac `\x. T` >> rw[listTheory.FILTER_T])
  >> simp[list_intersect_def] >>
  first_x_assum (qspec_then `FILTER (\x. MEM x h) bse` strip_assume_tac) >>
  qexists_tac `\x. P x /\ MEM x h` >>
  simp[rich_listTheory.FILTER_FILTER]
QED

(* Two FILTERs of an ALL_DISTINCT list with equal sets are equal *)
Theorem filter_set_eq_filter_eq_proof:
  !P Q bse. ALL_DISTINCT bse ==>
    set (FILTER P bse) = set (FILTER Q bse) ==>
    FILTER P bse = FILTER Q bse
Proof
  rpt strip_tac >>
  irule (GSYM rich_listTheory.FILTER_EQ |> iffLR) >>
  rpt strip_tac >>
  `MEM x (FILTER P bse) <=> MEM x (FILTER Q bse)` suffices_by
    simp[listTheory.MEM_FILTER] >>
  fs[pred_setTheory.EXTENSION]
QED

(* list_union: membership iff member of either list *)
Theorem list_union_mem_proof:
  !v xs ys. MEM v (list_union xs ys) <=> MEM v xs \/ MEM v ys
Proof
  rw[list_union_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

(* list_union: set semantics *)
Theorem list_union_set_proof:
  !xs ys. set (list_union xs ys) = set xs UNION set ys
Proof
  rw[list_union_def, LIST_TO_SET_APPEND, LIST_TO_SET_FILTER, EXTENSION] >>
  rw[MEM_FILTER] >> metis_tac[]
QED
