Theory readonlyInvokeCopyFwdHeterogeneousAllocation
Ancestors
  readonlyInvokeCopyFwdHeterogeneousMapOrigins readonlyInvokeCopyFwdHeterogeneousSupport
  readonlyInvokeCopyFwdAlignedOrigins readonlyInvokeCopyFwdOperationalAllocation
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistorySelected
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdRel
  occurrenceGeometry o1LowerDloadOccurrence ptrDiscipline
  finite_map list pred_set arithmetic

Theorem ricf_heterogeneous_alloca_support_fresh:
  ricf_heterogeneous_support_origins vs C a fn U stk B E /\
  occurrence_allocas_ok B a s /\ FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  (a,inst.inst_id) NOTIN E
Proof
  rw[ricf_heterogeneous_support_origins_def, occurrence_allocas_ok_def] >>
  strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ricf_heterogeneous_map_translation[local]:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  FLOOKUP sites key = SOME tr ==>
  ?ctxP logP. ricf_translation_origin vs C ctxP logP
    stk PG G tn fn inst s U B key tr
Proof
  rw[ricf_heterogeneous_map_origins_def] >> first_x_assum drule >>
  metis_tac[ricf_aligned_translation_origin_projection]
QED

Theorem ricf_heterogeneous_saved_map_translation[local]:
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  j < LENGTH stk /\ FLOOKUP (EL j maps) key = SOME tr ==>
  ?ctxP logP. ricf_translation_origin vs C ctxP logP
    stk PG G tn fn inst s U B key tr
Proof
  rw[ricf_heterogeneous_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >> metis_tac[ricf_aligned_origin_projection]
QED

Theorem ricf_heterogeneous_alloca_map_fresh:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  occurrence_natural_geometry lo a U B stk s ==>
  (s.vs_alloca_next,z) NOTIN FDOM sites
Proof
  strip_tac >> simp[GSYM FLOOKUP_DEF] >> strip_tac >>
  `?tr. FLOOKUP sites (s.vs_alloca_next,z) = SOME tr` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  drule_all ricf_heterogeneous_map_translation >> strip_tac >>
  qpat_assum `ricf_translation_origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_translation_origin_def]) >>
  `0 < p.rpe_size` by metis_tac[ricf_translation_positive] >>
  `p.rpe_db+p.rpe_size <= s.vs_alloca_next` by
    metis_tac[occurrence_natural_geometry_def] >> fs[]
QED

Theorem ricf_heterogeneous_allocation_certificate_bounds:
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  occurrence_natural_geometry lo a U B stk s /\
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  cur = ricf_phase_ranges 0 ledger /\ curs = ricf_phase_stack_ranges stk ledger ==>
  !gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
    (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next
Proof
  strip_tac >> gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- metis_tac[ricf_phase_allocation_bounds]
  >- (gvs[ricf_phase_stack_ranges_def, MEM_GENLIST] >>
      drule_all ricf_phase_allocation_bounds >> simp[ADD_COMM])
  >- (gvs[ricf_site_triples_def] >>
      drule_all ricf_heterogeneous_map_translation >> strip_tac >>
      drule_all ricf_translation_allocation_bounds >> simp[ADD_COMM]) >>
  gvs[ricf_site_triples_def] >>
  drule_all ricf_heterogeneous_saved_map_translation >> strip_tac >>
  drule_all ricf_translation_allocation_bounds >> simp[ADD_COMM]
QED

Theorem ricf_heterogeneous_cached_alloca_map_exclusion:
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) ==>
  (b,z) NOTIN FDOM sites
Proof
  strip_tac >> simp[GSYM FLOOKUP_DEF] >> strip_tac >>
  `?tr. FLOOKUP sites (b,z) = SOME tr` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  drule_all ricf_heterogeneous_map_translation >> strip_tac >>
  `0 < z` by
    (qpat_assum `ricf_translation_origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ricf_translation_origin_def]) >>
     gvs[] >> metis_tac[ricf_translation_positive]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    metis_tac[occ_frame_reachable_annotation] >>
  fs[occurrence_annotation_ok_def] >>
  `FLOOKUP B (a,aid) = SOME (b,z)` by fs[occurrence_allocas_ok_def] >>
  fs[ricf_translation_origin_def] >> gvs[] >>
  `MEM p.rpe_owner (MAP (\u. u.of_owner) U)` by
    (simp[MEM_MAP] >> qexists_tac `EL (LENGTH pre) U` >> simp[EL_MEM]) >>
  `p.rpe_dst <> (a,aid)` by (strip_tac >> gvs[]) >>
  `p.rpe_db+p.rpe_size <= p.rpe_db` by
    metis_tac[occurrence_geometry_sites_disjoint] >> decide_tac
QED
