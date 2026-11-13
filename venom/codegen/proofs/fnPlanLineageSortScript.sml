Theory fnPlanLineageSort
Ancestors
  sorting list rich_list

Theorem part_predicate_on[local]:
  !xs p q a b.
    (!x. MEM x xs ==> (p x = q x)) ==>
    PART p xs a b = PART q xs a b
Proof
  Induct >> simp[PART_DEF] >> rpt strip_tac >>
  `p h = q h` by metis_tac[] >> simp[] >>
  Cases_on `q h` >> simp[] >> first_x_assum irule >> metis_tac[]
QED

Theorem partition_predicate_on:
  !p q xs.
    (!x. MEM x xs ==> (p x = q x)) ==>
    PARTITION p xs = PARTITION q xs
Proof
  simp[PARTITION_DEF] >> metis_tac[part_predicate_on]
QED

Theorem partition_members:
  !p xs a b.
    PARTITION p xs = (a,b) ==>
    !x. MEM x xs = (MEM x a \/ MEM x b)
Proof
  rpt strip_tac >>
  qpat_x_assum `PARTITION _ _ = _` (mp_tac o GSYM) >>
  simp[PARTITION_DEF] >> strip_tac >> drule PART_MEM >> simp[]
QED

Theorem qsort_relation_on:
  !r xs s.
    (!x y. MEM x xs /\ MEM y xs ==> (r x y = s x y)) ==>
    QSORT r xs = QSORT s xs
Proof
  ho_match_mp_tac QSORT_IND >> conj_tac
  >- simp[QSORT_DEF] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `PARTITION (\y. r y h) t = PARTITION (\y. s y h) t` by
    (irule partition_predicate_on >> simp[] >> metis_tac[MEM]) >>
  simp[Once QSORT_DEF] >> pairarg_tac >> gvs[] >>
  `!x. MEM x t = (MEM x l1 \/ MEM x l2)` by
    (irule partition_members >> metis_tac[]) >>
  simp[Once QSORT_DEF] >>
  `QSORT r l1 = QSORT s l1` by (first_x_assum irule >> metis_tac[]) >>
  `QSORT r l2 = QSORT s l2` by (first_x_assum irule >> metis_tac[]) >> simp[]
QED
