Theory concretizePtrCandidateSeparation
Ancestors
  concretizeMemLocTransitionProofs concretizeMemLocDefs list finite_map enumeral
  execEquivParamDefs execEquivProofs

Theorem ptr_awl_untouched[local]:
  !pending global already initial.
  ~MEM a (MAP FST pending) ==>
  FLOOKUP (allocate_with_livesets global already pending initial) a = FLOOKUP initial a
Proof
  Induct >> simp[allocate_with_livesets_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[allocate_with_livesets_def] >> strip_tac >> pairarg_tac >>
  simp[FLOOKUP_UPDATE]
QED

Theorem ptr_awl_new_initial:
  !pending global already initial a la sa b lb pb sb pa.
  ALL_DISTINCT (MAP FST pending) /\
  (!c l s. MEM (c,l,s) pending ==> !l' p' s'. ~MEM (c,l',p',s') already) /\
  MEM (a,la,sa) pending /\ MEM (b,lb,pb,sb) already /\
  FLOOKUP (allocate_with_livesets global already pending initial) a = SOME pa /\
  sinter inst_addr_to lb la <> [] ==>
  pa + sa <= pb \/ pb + sb <= pa
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[allocate_with_livesets_def] >> pairarg_tac >> strip_tac >>
  gvs[]
  >- (`~MEM a (MAP FST pending)` by
        (fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      drule ptr_awl_untouched >> disch_then (qspecl_then
        [`global`,`already ++ [(a,h1,pos,h2)]`,`initial |+ (a,pos)`] mp_tac) >>
      simp[FLOOKUP_UPDATE] >> strip_tac >> gvs[] >>
      drule allocate_one_avoids >>
      disch_then (qspecl_then [`pb`,`sb`] mp_tac) >>
      simp[arithmeticTheory.ADD_COMM] >> impl_tac
      >- (simp[MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >>
          disj2_tac >> qexistsl_tac [`b`,`lb`] >> simp[]) >>
      simp[]) >>
  first_x_assum irule >> rpt (goal_assum (drule_at Any)) >>
  simp[] >> qexists `b` >> simp[] >> rpt gen_tac >> strip_tac >>
  fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem ptr_awl_new_new:
  !pending global already initial a la sa b lb sb pa pb.
  ALL_DISTINCT (MAP FST pending) /\
  (!c l s. MEM (c,l,s) pending ==> !l' p' s'. ~MEM (c,l',p',s') already) /\
  MEM (a,la,sa) pending /\ MEM (b,lb,sb) pending /\ a <> b /\
  FLOOKUP (allocate_with_livesets global already pending initial) a = SOME pa /\
  FLOOKUP (allocate_with_livesets global already pending initial) b = SOME pb /\
  sinter inst_addr_to la lb <> [] /\ sinter inst_addr_to lb la <> [] ==>
  pa + sa <= pb \/ pb + sb <= pa
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[allocate_with_livesets_def] >> pairarg_tac >> strip_tac >>
  gvs[]
  >- (drule ptr_awl_untouched >> disch_then (qspecl_then
        [`global`,`already ++ [(a,h1,pos,h2)]`,`initial |+ (a,pos)`] mp_tac) >>
      simp[FLOOKUP_UPDATE] >> strip_tac >> gvs[] >>
      `pb + sb <= pa \/ pa + h2 <= pb` suffices_by
        metis_tac[arithmeticTheory.ADD_COMM] >>
      irule ptr_awl_new_initial >> qexists `b` >>
      goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
      qexistsl_tac [`a`,`lb`,`h1`] >> simp[] >>
      rpt strip_tac >> fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[])
  >- (drule ptr_awl_untouched >> disch_then (qspecl_then
        [`global`,`already ++ [(b,h1,pos,h2)]`,`initial |+ (b,pos)`] mp_tac) >>
      simp[FLOOKUP_UPDATE] >> strip_tac >> gvs[] >>
      `pa + sa <= pb \/ pb + h2 <= pa` suffices_by
        metis_tac[arithmeticTheory.ADD_COMM] >>
      irule ptr_awl_new_initial >> qexists `a` >>
      goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
      qexistsl_tac [`b`,`la`,`h1`] >> simp[] >>
      rpt strip_tac >> fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  first_x_assum irule >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  qexistsl_tac [`la`,`lb`] >> simp[] >>
  rpt strip_tac >> fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED
