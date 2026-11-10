Theory basePtrConvergenceOrder
Ancestors
  list rich_list finite_map pred_set arithmetic venomInst basePtrDefs basePtrProofs

(* Growth forgets offsets but never changes an allocation.  Lists retain
   their relative order: their equality, not just their set, is observable. *)
Definition bp_ptr_le_def:
  bp_ptr_le p q <=>
    ptr_base p = ptr_base q /\
    (ptr_off p = ptr_off q \/ ptr_off q = NONE)
End

Inductive bp_list_le:
[~nil:]
  (!ys. bp_list_le [] ys)
[~skip:]
  (!xs ys y. bp_list_le xs ys ==> bp_list_le xs (y::ys))
[~cons:]
  (!x y xs ys. bp_ptr_le x y /\ bp_list_le xs ys ==>
                bp_list_le (x::xs) (y::ys))
End

Theorem bp_ptr_le_refl[simp]:
  bp_ptr_le p p
Proof
  simp[bp_ptr_le_def]
QED

Theorem bp_ptr_le_trans:
  bp_ptr_le p q /\ bp_ptr_le q r ==> bp_ptr_le p r
Proof
  simp[bp_ptr_le_def] >> metis_tac[]
QED

Theorem bp_list_le_refl[simp]:
  !xs. bp_list_le xs xs
Proof
  Induct >> simp[bp_list_le_rules]
QED

Theorem bp_list_le_trans:
  !ys zs. bp_list_le ys zs ==>
    !xs. bp_list_le xs ys ==> bp_list_le xs zs
Proof
  ho_match_mp_tac bp_list_le_ind >> rpt strip_tac
  >- (gvs[Once bp_list_le_cases] >> simp[bp_list_le_rules])
  >- metis_tac[bp_list_le_rules]
  >> qpat_x_assum `bp_list_le _ (_::_)` mp_tac
  >> once_rewrite_tac[bp_list_le_cases]
  >> strip_tac >> gvs[]
  >> metis_tac[bp_list_le_rules, bp_ptr_le_trans]
QED

Theorem bp_ptr_le_offset:
  bp_ptr_le p q ==> bp_ptr_le (offset_by p d) (offset_by q d)
Proof
  Cases_on `p` >> rename1 `Ptr a off` >>
  Cases_on `q` >> rename1 `bp_ptr_le (Ptr a off) (Ptr b off2)` >>
  Cases_on `off` >> Cases_on `off2` >> Cases_on `d` >>
  simp[bp_ptr_le_def, ptr_base_def, ptr_off_def, offset_by_def]
QED

Theorem bp_ptr_le_sub_offset:
  bp_ptr_le p q ==> bp_ptr_le (sub_offset_by p d) (sub_offset_by q d)
Proof
  Cases_on `p` >> rename1 `Ptr a off` >>
  Cases_on `q` >> rename1 `bp_ptr_le (Ptr a off) (Ptr b off2)` >>
  Cases_on `off` >> Cases_on `off2` >> Cases_on `d` >>
  simp[bp_ptr_le_def, ptr_base_def, ptr_off_def, sub_offset_by_def] >>
  rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >> simp[ptr_base_def, ptr_off_def]
QED

(* Embeddings are functorial for any pointer-growth preserving operation. *)
Theorem bp_list_le_map:
  (!p q. bp_ptr_le p q ==> bp_ptr_le (f p) (f q)) ==>
  !xs ys. bp_list_le xs ys ==> bp_list_le (MAP f xs) (MAP f ys)
Proof
  strip_tac >> ho_match_mp_tac bp_list_le_ind >>
  simp[bp_list_le_rules]
QED

Theorem bp_list_le_offset:
  bp_list_le xs ys ==>
  bp_list_le (MAP (\p. offset_by p d) xs) (MAP (\p. offset_by p d) ys)
Proof
  strip_tac >> irule bp_list_le_map >>
  simp[bp_ptr_le_offset] >> first_assum ACCEPT_TAC
QED

Theorem bp_list_le_sub_offset:
  bp_list_le xs ys ==>
  bp_list_le (MAP (\p. sub_offset_by p d) xs) (MAP (\p. sub_offset_by p d) ys)
Proof
  strip_tac >> irule bp_list_le_map >>
  simp[bp_ptr_le_sub_offset] >> first_assum ACCEPT_TAC
QED

(* The sequence of allocation names is the first-occurrence nub. *)
Theorem bp_normalize_bases:
  MAP ptr_base (bp_normalize ps) =
  REVERSE (nub (REVERSE (MAP ptr_base ps)))
Proof
  simp[bp_normalize_def, MAP_MAP_o, combinTheory.o_DEF] >>
  qmatch_goalsub_abbrev_tac `MAP f bs` >>
  `f = I` suffices_by (strip_tac >> gvs[]) >>
  simp[FUN_EQ_THM] >>
  gen_tac >> simp[Abbr `f`] >>
  CASE_TAC >> simp[ptr_base_def] >>
  CASE_TAC >> simp[ptr_base_def] >>
  CASE_TAC >> simp[ptr_base_def]
QED

Theorem bp_normalize_distinct_bases:
  ALL_DISTINCT (MAP ptr_base (bp_normalize ps))
Proof
  simp[bp_normalize_bases]
QED

Theorem bp_normalize_base_set:
  set (MAP ptr_base (bp_normalize ps)) = set (MAP ptr_base ps)
Proof
  simp[bp_normalize_bases]
QED

Theorem bp_normalize_base_prefix:
  ALL_DISTINCT (MAP ptr_base xs) ==>
  ?bs. MAP ptr_base (bp_normalize (xs ++ ys)) = MAP ptr_base xs ++ bs
Proof
  strip_tac >>
  simp[bp_normalize_bases, MAP_APPEND, REVERSE_APPEND, nub_append,
       all_distinct_nub_id]
QED

(* Coverage plus a common allocation prefix is enough for ordered growth. *)
Theorem bp_list_le_base_prefix:
  !xs ys bs.
    ALL_DISTINCT (MAP ptr_base ys) /\
    MAP ptr_base ys = MAP ptr_base xs ++ bs /\
    (!p. MEM p xs ==> ?q. MEM q ys /\ bp_ptr_le p q) ==>
    bp_list_le xs ys
Proof
  Induct >- simp[bp_list_le_rules] >>
  rpt gen_tac >> Cases_on `ys` >> simp[] >> strip_tac >>
  rename1 `ptr_base y = ptr_base h` >>
  `bp_ptr_le h y` by
    (first_x_assum (qspec_then `h` mp_tac) >> simp[] >> strip_tac >>
     gvs[bp_ptr_le_def] >>
     `MEM (ptr_base q) (MAP ptr_base t)` by
       (simp[MEM_MAP] >> metis_tac[]) >> gvs[]) >>
  irule (cj 3 bp_list_le_rules) >> simp[] >>
  first_x_assum irule >> simp[] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `p` mp_tac) >> simp[] >>
  strip_tac >- (gvs[bp_ptr_le_def] >>
    `MEM (ptr_base p) (MAP ptr_base xs)` by
      (simp[MEM_MAP] >> metis_tac[]) >> gvs[]) >>
  metis_tac[]
QED

Theorem bp_normalize_prefix_growth:
  ALL_DISTINCT (MAP ptr_base xs) ==>
  bp_list_le xs (bp_normalize (xs ++ ys))
Proof
  strip_tac >> drule bp_normalize_base_prefix >> strip_tac >>
  irule bp_list_le_base_prefix >>
  simp[bp_normalize_distinct_bases] >> rpt strip_tac >>
  `MEM p (xs ++ ys)` by simp[] >>
  drule bp_normalize_covers >> strip_tac >>
  qexists_tac `q` >> simp[] >> gvs[bp_ptr_le_def, ptr_base_def, ptr_off_def]
QED

(* Each list cell contributes one, and losing its exact offset contributes
   one more.  No bound on the value of a numeric offset is required. *)
Definition bp_ptr_rank_def:
  bp_ptr_rank p : num = if ptr_off p = NONE then 2 else 1
End

Definition bp_list_rank_def:
  bp_list_rank ps = SUM (MAP bp_ptr_rank ps)
End

Theorem bp_ptr_rank_bounds:
  0 < bp_ptr_rank p /\ bp_ptr_rank p <= 2
Proof
  simp[bp_ptr_rank_def] >> IF_CASES_TAC >> simp[]
QED

Theorem bp_ptr_rank_growth:
  bp_ptr_le p q ==>
  bp_ptr_rank p <= bp_ptr_rank q /\
  (bp_ptr_rank p = bp_ptr_rank q ==> p = q)
Proof
  Cases_on `p` >> rename1 `Ptr a off` >>
  Cases_on `q` >> rename1 `bp_ptr_le (Ptr a off) (Ptr b off2)` >>
  Cases_on `off` >> Cases_on `off2` >>
  simp[bp_ptr_rank_def, bp_ptr_le_def, ptr_off_def, ptr_base_def]
QED

Theorem bp_list_rank_nil[simp]:
  bp_list_rank [] = 0
Proof
  simp[bp_list_rank_def]
QED

Theorem bp_list_rank_cons[simp]:
  bp_list_rank (p::ps) = bp_ptr_rank p + bp_list_rank ps
Proof
  simp[bp_list_rank_def]
QED

Theorem bp_list_rank_growth:
  !xs ys. bp_list_le xs ys ==>
  bp_list_rank xs <= bp_list_rank ys /\
  (bp_list_rank xs = bp_list_rank ys ==> xs = ys)
Proof
  ho_match_mp_tac bp_list_le_ind >> rpt conj_tac
  >- (Induct >> simp[] >> gen_tac >>
      qspec_then `h` mp_tac (GEN_ALL bp_ptr_rank_bounds) >> simp[])
  >- (rpt strip_tac >> gvs[] >>
      qspec_then `y` mp_tac (GEN_ALL bp_ptr_rank_bounds) >> decide_tac)
  >> rpt gen_tac >> strip_tac >> drule bp_ptr_rank_growth >>
  simp[] >> strip_tac >> conj_tac
QED

Theorem bp_list_rank_bound:
  !ps. bp_list_rank ps <= 2 * LENGTH ps
Proof
  Induct >> simp[] >> gen_tac >>
  qspec_then `h` mp_tac (GEN_ALL bp_ptr_rank_bounds) >> decide_tac
QED

Definition bp_map_le_def:
  bp_map_le (r : bp_result) s <=>
    FDOM r SUBSET FDOM s /\
    !v. bp_list_le (bp_get_ptrs r v) (bp_get_ptrs s v)
End

Definition bp_map_wf_def:
  bp_map_wf V A (r : bp_result) <=>
    FDOM r SUBSET V /\
    !v. ALL_DISTINCT (MAP ptr_base (bp_get_ptrs r v)) /\
        set (MAP ptr_base (bp_get_ptrs r v)) SUBSET A
End

Definition bp_map_rank_def:
  bp_map_rank (r : bp_result) =
    CARD (FDOM r) + SIGMA (\v. bp_list_rank (bp_get_ptrs r v)) (FDOM r)
End

Theorem bp_map_le_refl[simp]:
  bp_map_le r r
Proof
  simp[bp_map_le_def]
QED

Theorem bp_map_le_trans:
  bp_map_le r s /\ bp_map_le s t ==> bp_map_le r t
Proof
  simp[bp_map_le_def, bp_get_ptrs_update] >> rpt strip_tac
  >- metis_tac[SUBSET_TRANS]
  >> metis_tac[bp_list_le_trans]
QED

Theorem bp_map_le_empty[simp]:
  bp_map_le FEMPTY r
Proof
  simp[bp_map_le_def, bp_get_ptrs_def, bp_list_le_rules]
QED

Theorem bp_map_wf_empty[simp]:
  bp_map_wf V A FEMPTY
Proof
  simp[bp_map_wf_def, bp_get_ptrs_def]
QED

Theorem bp_map_le_update:
  bp_map_le r s /\ bp_list_le ps qs ==>
  bp_map_le (r |+ (v,ps)) (s |+ (v,qs))
Proof
  simp[bp_map_le_def, bp_get_ptrs_update] >> rpt strip_tac
  >- ASM_SET_TAC[]
  >> IF_CASES_TAC >> simp[]
QED

Theorem bp_map_le_write:
  bp_list_le (bp_get_ptrs r v) ps ==> bp_map_le r (r |+ (v,ps))
Proof
  simp[bp_map_le_def, bp_get_ptrs_update] >> rpt strip_tac
  >- SET_TAC[]
  >> IF_CASES_TAC >> simp[]
QED

Theorem bp_map_wf_update:
  bp_map_wf V A r /\ v IN V /\ ALL_DISTINCT (MAP ptr_base ps) /\
  set (MAP ptr_base ps) SUBSET A ==>
  bp_map_wf V A (r |+ (v,ps))
Proof
  simp[bp_map_wf_def, bp_get_ptrs_update] >> rpt strip_tac
  >- ASM_SET_TAC[]
  >> IF_CASES_TAC >> simp[]
QED

Theorem bp_list_rank_support_bound:
  FINITE A /\ ALL_DISTINCT (MAP ptr_base ps) /\
  set (MAP ptr_base ps) SUBSET A ==>
  bp_list_rank ps <= 2 * CARD A
Proof
  rpt strip_tac >>
  `LENGTH ps <= CARD A` by
    (drule CARD_SUBSET >>
     disch_then (qspec_then `set (MAP ptr_base ps)` mp_tac) >>
     simp[ALL_DISTINCT_CARD_LIST_TO_SET]) >>
  qspec_then `ps` mp_tac bp_list_rank_bound >> decide_tac
QED

Theorem bp_map_rank_bound:
  FINITE V /\ FINITE A /\ bp_map_wf V A r ==>
  bp_map_rank r <= CARD V * (1 + 2 * CARD A)
Proof
  simp[bp_map_wf_def, bp_map_rank_def] >> rpt strip_tac >>
  `CARD (FDOM r) <= CARD V` by metis_tac[CARD_SUBSET] >>
  `SIGMA (\v. bp_list_rank (bp_get_ptrs r v)) (FDOM r) <=
   CARD (FDOM r) * (2 * CARD A)` by
    (irule SUM_IMAGE_upper_bound >> simp[] >>
     rpt strip_tac >> irule bp_list_rank_support_bound >> simp[]) >>
  irule LESS_EQ_TRANS >>
  qexists_tac `CARD (FDOM r) * (1 + 2 * CARD A)` >>
  reverse conj_tac >- simp[] >>
  simp[LEFT_ADD_DISTRIB]
QED

Theorem bp_map_rank_mono:
  bp_map_le r s ==> bp_map_rank r <= bp_map_rank s
Proof
  simp[bp_map_le_def, bp_map_rank_def] >> strip_tac >>
  `CARD (FDOM r) <= CARD (FDOM s)` by metis_tac[CARD_SUBSET, FDOM_FINITE] >>
  `SIGMA (\v. bp_list_rank (bp_get_ptrs r v)) (FDOM r) <=
   SIGMA (\v. bp_list_rank (bp_get_ptrs s v)) (FDOM r)` by
    (irule SUM_IMAGE_MONO_LESS_EQ >> simp[] >>
     metis_tac[bp_list_rank_growth]) >>
  `SIGMA (\v. bp_list_rank (bp_get_ptrs s v)) (FDOM r) <=
   SIGMA (\v. bp_list_rank (bp_get_ptrs s v)) (FDOM s)` by
    (irule SUM_IMAGE_SUBSET_LE >> simp[]) >> decide_tac
QED

(* The following equality interface deliberately includes the domain:
   a missing binding is different from a stored empty list. *)
Theorem bp_map_eq:
  FDOM r = FDOM s /\ (!v. bp_get_ptrs r v = bp_get_ptrs s v) ==> r = s
Proof
  strip_tac >> simp[fmap_eq_flookup] >> gen_tac >>
  Cases_on `FLOOKUP r x` >> Cases_on `FLOOKUP s x` >>
  gvs[FLOOKUP_DEF, bp_get_ptrs_def] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem bp_map_rank_eq:
  bp_map_le r s /\ bp_map_rank r = bp_map_rank s ==> r = s
Proof
  simp[bp_map_le_def, bp_map_rank_def] >> strip_tac >>
  `CARD (FDOM r) <= CARD (FDOM s)` by metis_tac[CARD_SUBSET, FDOM_FINITE] >>
  `SIGMA (\v. bp_list_rank (bp_get_ptrs r v)) (FDOM r) <=
   SIGMA (\v. bp_list_rank (bp_get_ptrs s v)) (FDOM r)` by
    (irule SUM_IMAGE_MONO_LESS_EQ >> simp[] >>
     metis_tac[bp_list_rank_growth]) >>
  `SIGMA (\v. bp_list_rank (bp_get_ptrs s v)) (FDOM r) <=
   SIGMA (\v. bp_list_rank (bp_get_ptrs s v)) (FDOM s)` by
    (irule SUM_IMAGE_SUBSET_LE >> simp[]) >>
  `CARD (FDOM r) = CARD (FDOM s)` by decide_tac >>
  `FDOM r = FDOM s` by metis_tac[cardinalityCoreTheory.CARD_SUBSET_EQ, FDOM_FINITE] >>
  irule bp_map_eq >> simp[] >> gen_tac >>
  Cases_on `v IN FDOM s`
  >- (spose_not_then assume_tac >>
      `bp_list_rank (bp_get_ptrs r v) < bp_list_rank (bp_get_ptrs s v)` by
        (first_x_assum (qspec_then `v` mp_tac) >>
         disch_then (mp_tac o MATCH_MP bp_list_rank_growth) >> simp[] >> decide_tac) >>
      `SIGMA (\v. bp_list_rank (bp_get_ptrs r v)) (FDOM s) <
       SIGMA (\v. bp_list_rank (bp_get_ptrs s v)) (FDOM s)` by
        (irule SUM_IMAGE_MONO_LESS >> simp[] >> conj_tac
         >- metis_tac[bp_list_rank_growth] >>
         qexists_tac `v` >> simp[]) >> gvs[]) >>
  fs[bp_get_ptrs_def, FLOOKUP_DEF]
QED

Theorem bp_map_rank_strict:
  bp_map_le r s /\ r <> s ==> bp_map_rank r < bp_map_rank s
Proof
  metis_tac[bp_map_rank_mono, bp_map_rank_eq, LESS_OR_EQ]
QED

Theorem bp_list_rank_formula:
  !ps. bp_list_rank ps = LENGTH ps + LENGTH (FILTER (\p. ptr_off p = NONE) ps)
Proof
  Induct >> simp[] >> gen_tac >>
  simp[bp_ptr_rank_def] >> IF_CASES_TAC >> simp[]
QED
