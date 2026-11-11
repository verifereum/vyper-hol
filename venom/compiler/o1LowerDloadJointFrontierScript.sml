Theory o1LowerDloadJointFrontier
Ancestors
  o1LowerDloadStackFrontier o1LowerDloadJointRelation finite_map pred_set list

Theorem ld_scratch_credit_mono:
  (!a. MEM a owners ==> MEM a ambient) ==>
  CARD {id | id IN FDOM X /\ MEM (FST id) owners} <=
  CARD {id | id IN FDOM X /\ MEM (FST id) ambient}
Proof
  strip_tac >> irule CARD_SUBSET >> conj_tac
  >- (irule SUBSET_FINITE >> qexists_tac `FDOM X` >> simp[SUBSET_DEF]) >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_joint_frame_frontiers:
  ld_joint_frame sites X lo owner older u fn fn' H HP tv s t ==>
  (!aid b c z. FLOOKUP sites (owner,aid) = SOME (b,c,z) ==>
     b+z <= s.vs_alloca_next /\ c+z <= t.vs_alloca_next) /\
  (!did aid c. FLOOKUP X (owner,did) = SOME (aid,c) ==>
     c+32 <= t.vs_alloca_next) /\
  t.vs_alloca_next = s.vs_alloca_next +
    32 * CARD {id | id IN FDOM X /\ MEM (FST id) (owner::older)}
Proof
  rewrite_tac[ld_joint_frame_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem ld_joint_saved_frontiers:
  !U stk ts.
  ld_joint_saved C' sites X lo U stk ts /\
  EVERY (\f. f.cf_state.vs_alloca_next <= N) stk /\
  (!a. MEM a (MAP (\x. x.of_owner) U) ==> MEM a ambient) ==>
  (!jd b c z. MEM (FST jd) (MAP (\x. x.of_owner) U) /\
     FLOOKUP sites jd = SOME (b,c,z) ==>
     b+z <= N /\ c+z <= N +
       32 * CARD {id | id IN FDOM X /\ MEM (FST id) ambient}) /\
  (!jd aid c. MEM (FST jd) (MAP (\x. x.of_owner) U) /\
     FLOOKUP X jd = SOME (aid,c) ==>
     c+32 <= N + 32 * CARD {id | id IN FDOM X /\ MEM (FST id) ambient})
Proof
  Induct >> simp[ld_joint_saved_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule ld_joint_frame_frontiers >> strip_tac >>
  `CARD {id | id IN FDOM X /\ MEM (FST id) (h.of_owner::MAP (\x. x.of_owner) U)} <=
   CARD {id | id IN FDOM X /\ MEM (FST id) ambient}` by
    (irule ld_scratch_credit_mono >> simp[] >> metis_tac[]) >>
  `t.vs_alloca_next <= N + 32 * CARD {id | id IN FDOM X /\ MEM (FST id) ambient}` by
    decide_tac >>
  first_x_assum (qspecl_then [`fs`, `rest`] mp_tac) >> simp[] >> strip_tac >>
  conj_tac
  >- (qx_gen_tac `jd` >> PairCases_on `jd` >> rpt gen_tac >> strip_tac >>
      Cases_on `jd0 = h.of_owner`
      >- (fs[] >> qpat_x_assum `!aid b c z. _` drule >> strip_tac >> decide_tac) >>
      first_x_assum (qspec_then `(jd0,jd1)` mp_tac) >> simp[] >>
      metis_tac[]) >>
  qx_gen_tac `jd` >> PairCases_on `jd` >> rpt gen_tac >> strip_tac >>
  Cases_on `jd0 = h.of_owner`
  >- (fs[] >> qpat_x_assum `!did aid c. _` drule >> strip_tac >> decide_tac) >>
  first_x_assum (qspec_then `(jd0,jd1)` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ld_joint_boundary_saved_frontiers:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  (!jd b c z. MEM (FST jd) (MAP (\x. x.of_owner) U) /\
     FLOOKUP sites jd = SOME (b,c,z) ==>
     b+z <= s.vs_alloca_next /\ c+z <= t.vs_alloca_next) /\
  (!jd aid c. MEM (FST jd) (MAP (\x. x.of_owner) U) /\
     FLOOKUP X jd = SOME (aid,c) ==> c+32 <= t.vs_alloca_next)
Proof
  rewrite_tac[ld_joint_boundary_def] >> strip_tac >>
  drule ld_occ_saved_frontiers >> strip_tac >>
  drule ld_joint_saved_frontiers >>
  disch_then (qspecl_then [`a::MAP (\x. x.of_owner) U`, `s.vs_alloca_next`] mp_tac) >>
  simp[] >> strip_tac >> drule ld_joint_frame_frontiers >> strip_tac >>
  gvs[] >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem ld_joint_boundary_site_frontiers:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  !jd d e w. FLOOKUP sites jd = SOME (d,e,w) ==>
    d+w <= s.vs_alloca_next /\ e+w <= t.vs_alloca_next
Proof
  strip_tac >> drule ld_joint_boundary_saved_frontiers >> strip_tac >>
  qhdtm_x_assum `ld_joint_boundary` mp_tac >> rewrite_tac[ld_joint_boundary_def] >> strip_tac >>
  drule ld_joint_frame_frontiers >> strip_tac >>
  qx_gen_tac `jd` >> PairCases_on `jd` >> rpt gen_tac >> disch_tac >>
  Cases_on `jd0 = a`
  >- (gvs[] >> qpat_x_assum `!aid b c z. FLOOKUP sites (a,aid) = _ ==> _` drule >> simp[]) >>
  `MEM jd0 (MAP (\x. x.of_owner) U)` by
    (fs[ld_joint_geometry_def] >>
     qpat_x_assum `!id. id IN FDOM sites \/ id IN FDOM X ==> _` (qspec_then `(jd0,jd1)` mp_tac) >>
     gvs[FLOOKUP_DEF]) >>
  qpat_x_assum `!jd b c z. MEM _ _ /\ _ ==> _`
    (qspecl_then [`(jd0,jd1)`, `d`, `e`, `w`] mp_tac) >> simp[]
QED

Theorem ld_joint_boundary_scratch_frontier:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  !jd aid e. FLOOKUP X jd = SOME (aid,e) ==> e+32 <= t.vs_alloca_next
Proof
  strip_tac >> drule ld_joint_boundary_saved_frontiers >> strip_tac >>
  qhdtm_x_assum `ld_joint_boundary` mp_tac >> rewrite_tac[ld_joint_boundary_def] >> strip_tac >>
  drule ld_joint_frame_frontiers >> strip_tac >>
  qx_gen_tac `jd` >> PairCases_on `jd` >> rpt gen_tac >> disch_tac >>
  Cases_on `jd0 = a`
  >- (gvs[] >> qpat_x_assum `!did aid c. FLOOKUP X (a,did) = _ ==> _` drule >> simp[]) >>
  `MEM jd0 (MAP (\x. x.of_owner) U)` by
    (fs[ld_joint_geometry_def] >>
     qpat_x_assum `!id. id IN FDOM sites \/ id IN FDOM X ==> _` (qspec_then `(jd0,jd1)` mp_tac) >>
     gvs[FLOOKUP_DEF]) >>
  qpat_x_assum `!jd aid c. MEM _ _ /\ _ ==> _`
    (qspecl_then [`(jd0,jd1)`, `aid`, `e`] mp_tac) >> simp[]
QED
