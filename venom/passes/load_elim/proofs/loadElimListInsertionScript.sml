Theory loadElimListInsertion
Ancestors
  list rich_list sorting pred_set

Theorem le_filtered_routing_distinct:
  !labels actions key target.
  ALL_DISTINCT labels /\ ALL_DISTINCT (MAP key actions) ==>
  ALL_DISTINCT (FLAT (MAP (\lbl. MAP key (FILTER (\a. target a = lbl) actions)) labels))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[ALL_DISTINCT_APPEND] >>
  conj_tac >- (qpat_x_assum `ALL_DISTINCT (MAP key actions)` mp_tac >>
    Induct_on `actions` >> simp[] >> rpt strip_tac >>
    IF_CASES_TAC >> gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  simp[MEM_MAP, MEM_FILTER, MEM_FLAT] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  gvs[MEM_MAP, MEM_FILTER] >>
  qpat_x_assum `ALL_DISTINCT (MAP key actions)` mp_tac >>
  Induct_on `actions` >> simp[MEM_MAP] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem le_insert_perm:
  !xs ys n. PERM (TAKE n xs ++ ys ++ DROP n xs) (xs ++ ys)
Proof
  rpt gen_tac >>
  irule PERM_TRANS >>
  qexists_tac `TAKE n xs ++ DROP n xs ++ ys` >>
  conj_tac >- (rewrite_tac[GSYM APPEND_ASSOC] >>
    irule PERM_CONG >> simp[PERM_APPEND]) >>
  simp[TAKE_DROP]
QED

Theorem le_flat_insert_perm:
  !bs old added cut.
  PERM (FLAT (MAP (\b. TAKE (cut b) (old b) ++ added b ++ DROP (cut b) (old b)) bs))
       (FLAT (MAP old bs) ++ FLAT (MAP added bs))
Proof
  Induct >- simp[] >> rpt gen_tac >> pure_rewrite_tac[MAP, FLAT] >>
  irule PERM_TRANS >>
  qexists_tac `(old h ++ added h) ++ (FLAT (MAP old bs) ++ FLAT (MAP added bs))` >>
  conj_tac >- (irule PERM_CONG >> simp[le_insert_perm]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, PERM_APPEND_IFF] >>
  simp[PERM_SWAP_L_AT_FRONT]
QED

Theorem le_flat_insert_distinct:
  ALL_DISTINCT (FLAT (MAP old bs)) /\
  ALL_DISTINCT (FLAT (MAP added bs)) /\
  (!x. MEM x (FLAT (MAP old bs)) ==> ~MEM x (FLAT (MAP added bs))) ==>
  ALL_DISTINCT (FLAT (MAP (\b. TAKE (cut b) (old b) ++ added b ++ DROP (cut b) (old b)) bs))
Proof
  metis_tac[le_flat_insert_perm, ALL_DISTINCT_PERM, ALL_DISTINCT_APPEND]
QED

Theorem le_flat_insert_projection_perm:
  !bs old added cut project.
  PERM
    (FLAT (MAP (\b. FLAT (MAP project
      (TAKE (cut b) (old b) ++ added b ++ DROP (cut b) (old b)))) bs))
    (FLAT (MAP (\b. FLAT (MAP project (old b))) bs) ++
     FLAT (MAP (\b. FLAT (MAP project (added b))) bs))
Proof
  rpt gen_tac >>
  mp_tac le_flat_insert_perm >>
  disch_then (qspecl_then [`bs`, `old`, `added`, `cut`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP (Q.ISPEC `project : 'b -> 'c list` PERM_MAP)) >>
  disch_then (mp_tac o MATCH_MP PERM_FLAT) >>
  simp[MAP_FLAT, MAP_MAP_o, FLAT_APPEND, MAP_APPEND, FLAT_FLAT, combinTheory.o_DEF]
QED

Theorem le_flat_insert_projection_distinct:
  ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP project (old b))) bs)) /\
  ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP project (added b))) bs)) /\
  (!x. MEM x (FLAT (MAP (\b. FLAT (MAP project (old b))) bs)) ==>
       ~MEM x (FLAT (MAP (\b. FLAT (MAP project (added b))) bs))) ==>
  ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP project
    (TAKE (cut b) (old b) ++ added b ++ DROP (cut b) (old b)))) bs))
Proof
  metis_tac[le_flat_insert_projection_perm, ALL_DISTINCT_PERM, ALL_DISTINCT_APPEND]
QED
