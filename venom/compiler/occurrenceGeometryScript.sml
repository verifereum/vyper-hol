(* Natural allocation intervals and ordered saved-frame cuts.
   No machine-word representability is required by this geometry. *)
Theory occurrenceGeometry
Ancestors
  o1LowerDloadOccurrence finite_map list pred_set arithmetic

Definition occurrence_natural_geometry_def:
  occurrence_natural_geometry lo a U B stk s <=>
    (!id b z. FLOOKUP B id = SOME (b,z) ==>
       lo <= b /\ b + z <= s.vs_alloca_next) /\
    (!id jd b z c w.
       FLOOKUP B id = SOME (b,z) /\ FLOOKUP B jd = SOME (c,w) /\
       id <> jd /\ 0 < z /\ 0 < w ==> b + z <= c \/ c + w <= b) /\
    LENGTH U = LENGTH stk /\
    (!j. j < LENGTH stk ==>
       (EL j stk).cf_state.vs_alloca_next <= s.vs_alloca_next /\
       (!id b z. FLOOKUP B id = SOME (b,z) /\
          MEM (FST id) (MAP (\u. u.of_owner) (DROP j U)) ==>
          b + z <= (EL j stk).cf_state.vs_alloca_next) /\
       (!id b z. FLOOKUP B id = SOME (b,z) /\
          (FST id = a \/ MEM (FST id) (MAP (\u. u.of_owner) (TAKE j U))) ==>
          (EL j stk).cf_state.vs_alloca_next <= b)) /\
    (!i j. i < j /\ j < LENGTH stk ==>
       (EL j stk).cf_state.vs_alloca_next <= (EL i stk).cf_state.vs_alloca_next)
End

Theorem occurrence_natural_geometry_empty:
  occurrence_natural_geometry lo a [] FEMPTY [] s
Proof
  simp[occurrence_natural_geometry_def]
QED

Theorem occurrence_natural_geometry_same_frontier:
  occurrence_natural_geometry lo a U B stk s /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  occurrence_natural_geometry lo a U B stk t
Proof
  strip_tac >> gvs[occurrence_natural_geometry_def] >> metis_tac[]
QED

Theorem occurrence_natural_geometry_grow_frontier:
  occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  occurrence_natural_geometry lo a U B stk t
Proof
  rw[occurrence_natural_geometry_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem occurrence_natural_geometry_extend:
  occurrence_natural_geometry lo a U B stk s /\
  ~MEM a (MAP (\u. u.of_owner) U) /\
  (a,aid) NOTIN FDOM B /\ lo <= s.vs_alloca_next /\
  t.vs_alloca_next = s.vs_alloca_next + z ==>
  occurrence_natural_geometry lo a U
    (B |+ ((a,aid),(s.vs_alloca_next,z))) stk t
Proof
  strip_tac >> fs[occurrence_natural_geometry_def] >>
  simp[occurrence_natural_geometry_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `id = (a,aid)` >> gvs[FLOOKUP_UPDATE] >>
      qpat_x_assum `!id b z. FLOOKUP B id = SOME (b,z) ==> _` drule >>
      strip_tac >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `id = (a,aid)`
      >- (gvs[FLOOKUP_UPDATE] >>
          qpat_x_assum `!id b z. FLOOKUP B id = SOME (b,z) ==> _` drule >> simp[]) >>
      Cases_on `jd = (a,aid)`
      >- (gvs[FLOOKUP_UPDATE] >>
          qpat_x_assum `!id b z. FLOOKUP B id = SOME (b,z) ==> _` drule >> simp[]) >>
      gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _` drule >> strip_tac >>
  conj_tac >- simp[] >>
  `~MEM a (MAP (\u. u.of_owner) (DROP j U))` by
    (simp[MAP_DROP] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `id = (a,aid)` >> gvs[FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  rpt strip_tac >> Cases_on `id = (a,aid)` >> gvs[FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem occurrence_natural_geometry_push:
  occurrence_natural_geometry lo a U B stk s /\
  (!id. id IN FDOM B ==> MEM (FST id) (a::MAP (\u. u.of_owner) U)) /\
  ~MEM c (a::MAP (\u. u.of_owner) U) /\
  u.of_owner = a /\ f.cf_state.vs_alloca_next = s.vs_alloca_next /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  occurrence_natural_geometry lo c (u::U) B (f::stk) t
Proof
  strip_tac >>
  `!id b z. FLOOKUP B id = SOME (b,z) ==> FST id <> c` by
    (rpt strip_tac >> `id IN FDOM B` by fs[FLOOKUP_DEF] >> metis_tac[]) >>
  fs[occurrence_natural_geometry_def] >>
  simp[occurrence_natural_geometry_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (Cases >> simp[]
      >- (rpt strip_tac >> metis_tac[FLOOKUP_DEF]) >>
      rpt strip_tac >>
      qpat_x_assum `!j. j < LENGTH stk ==> _` drule >>
      strip_tac >> simp[] >> rpt strip_tac >>
      metis_tac[FLOOKUP_DEF]) >>
  Cases >> Cases >> simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem occurrence_natural_geometry_pop:
  occurrence_natural_geometry lo a (u::U) B (f::stk) s /\
  (!id. id IN FDOM B ==> MEM (FST id) (a::MAP (\u. u.of_owner) (u::U))) /\
  t.vs_alloca_next = f.cf_state.vs_alloca_next ==>
  occurrence_natural_geometry lo u.of_owner U
    (DRESTRICT B {id | FST id <> a}) stk t
Proof
  strip_tac >> fs[occurrence_natural_geometry_def] >>
  `!id b z. FLOOKUP (DRESTRICT B {id | FST id <> a}) id = SOME (b,z) ==>
     FLOOKUP B id = SOME (b,z) /\
     MEM (FST id) (MAP (\u. u.of_owner) (u::U))` by
    (simp[FLOOKUP_DRESTRICT] >> rpt strip_tac >>
     `id IN FDOM B` by fs[FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_assum `!j. j < SUC (LENGTH stk) ==> _`
    (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  simp[occurrence_natural_geometry_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_x_assum `!id b z. FLOOKUP (DRESTRICT _ _) id = _ ==> _` drule >>
      simp[] >> strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> fs[FLOOKUP_DRESTRICT] >> metis_tac[]) >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!j. j < SUC (LENGTH stk) ==> _`
        (qspec_then `SUC j` mp_tac) >> simp[] >> strip_tac >>
      conj_tac >- (qpat_x_assum `!i j. _` (qspecl_then [`0`,`SUC j`] mp_tac) >> simp[]) >>
      conj_tac >- (rpt strip_tac >> fs[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
      rpt strip_tac >> fs[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!i j. _` (qspecl_then [`SUC i`,`SUC j`] mp_tac) >> simp[]
QED

(* Definition probes: zero-size sites and natural bases beyond word256. *)
Theorem occurrence_natural_geometry_zero_wrap_probe[local]:
  occurrence_natural_geometry 0 0 []
    (FEMPTY |+ ((0,0),(2 ** 256,0))) []
    (s with vs_alloca_next := 2 ** 256) /\
  occurrence_natural_geometry 0 0 []
    (FEMPTY |+ ((0,0),(2 ** 256,1))) []
    (s with vs_alloca_next := 2 ** 256 + 1)
Proof
  simp[occurrence_natural_geometry_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED
