Theory lowerDloadScratchGeometry
Ancestors
  lowerDloadLifetime lowerDloadAllocation venomMemDefs ptrDiscipline finite_map words pred_set

Theorem ld_scratch_geometry:
  ld_alloc_account keys d0 A s t /\ id IN keys /\
  allocas_non_overlapping t /\ alloca_next_valid t /\ allocas_from lo t /\
  lo <= t.vs_alloca_next /\ t.vs_alloca_next < dimword (:256) /\
  (id NOTIN A ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    if FST owner = frame then
      FLOOKUP s.vs_allocas (SND owner) = SOME (bs,sz) /\
      FLOOKUP t.vs_allocas (SND owner) = SOME (bt,sz)
    else bt + sz <= lo) ==>
  ?p. p + 32 < dimword (:256) /\
    ((FLOOKUP t.vs_allocas id = NONE /\ p = t.vs_alloca_next) \/
      FLOOKUP t.vs_allocas id = SOME (p,32)) /\
    (!a b. ld_site_bytes E live a b ==> b < p \/ p + 32 <= b)
Proof
  strip_tac >> Cases_on `id IN A`
  >- (drule_all ld_alloc_account_scratch_entry >> strip_tac >>
      rename1 `FLOOKUP t.vs_allocas id = SOME (p,32)` >>
      `p + 32 <= t.vs_alloca_next /\ lo <= p` by
        metis_tac[alloca_next_valid_def, allocas_from_def] >>
      qexists_tac `p` >> simp[] >>
      rpt gen_tac >> simp[ld_site_bytes_def] >> strip_tac >>
      first_x_assum drule >> disch_then drule >>
      Cases_on `FST owner = frame` >> simp[] >> strip_tac
      >- (drule ld_alloc_account_disjoint >> strip_tac >>
          `SND owner <> id` by
            (gvs[DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
          `bt + sz <= p \/ p + 32 <= bt` by
            metis_tac[allocas_non_overlapping_def] >> decide_tac) >>
      decide_tac) >>
  `FLOOKUP t.vs_allocas id = NONE` by
    metis_tac[ld_alloc_account_scratch_absent] >>
  qexists_tac `t.vs_alloca_next` >> simp[] >>
  rpt gen_tac >> simp[ld_site_bytes_def] >> strip_tac >>
  first_x_assum drule >> disch_then drule >>
  Cases_on `FST owner = frame` >> simp[] >> strip_tac
  >- (`bt + sz <= t.vs_alloca_next` by metis_tac[alloca_next_valid_def] >>
      decide_tac) >>
  decide_tac
QED
