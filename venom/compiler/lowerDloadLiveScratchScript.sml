Theory lowerDloadLiveScratch
Ancestors
  lowerDloadLifetime lowerDloadAllocation venomMemDefs ptrDiscipline finite_map words pred_set

Theorem ld_live_scratch_separation_floor:
  ld_alloc_account keys d0 A s t /\ id IN keys /\ lo <= f /\
  allocas_non_overlapping t /\ alloca_next_valid t /\ allocas_from f t /\
  f <= t.vs_alloca_next /\ t.vs_alloca_next < dimword (:256) /\
  (id NOTIN A ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt + sz <= f \/
    (?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME (bt,sz))) ==>
  ?p. f <= p /\ p + 32 < dimword (:256) /\
    ((FLOOKUP t.vs_allocas id = NONE /\ p = t.vs_alloca_next) \/
      FLOOKUP t.vs_allocas id = SOME (p,32)) /\
    (!aa bb. ((aa = bb /\ aa < lo) \/ ld_site_bytes E live aa bb) ==>
      bb < p \/ p + 32 <= bb)
Proof
  strip_tac >> Cases_on `id IN A`
  >- (drule_all ld_alloc_account_scratch_entry >> strip_tac >>
      rename1 `FLOOKUP t.vs_allocas id = SOME (p,32)` >>
      `p + 32 <= t.vs_alloca_next /\ f <= p` by
        metis_tac[alloca_next_valid_def, allocas_from_def] >>
      qexists_tac `p` >> simp[] >>
      rpt gen_tac >> strip_tac
      >- decide_tac >>
      gvs[ld_site_bytes_def] >>
      first_x_assum drule >> disch_then drule >> strip_tac
      >- decide_tac >>
      `j <> id` by metis_tac[] >>
      `bt + sz <= p \/ p + 32 <= bt` by
        metis_tac[allocas_non_overlapping_def] >> decide_tac) >>
  `FLOOKUP t.vs_allocas id = NONE` by
    metis_tac[ld_alloc_account_scratch_absent] >>
  qexists_tac `t.vs_alloca_next` >> simp[] >>
  rpt gen_tac >> strip_tac
  >- decide_tac >>
  gvs[ld_site_bytes_def] >>
  first_x_assum drule >> disch_then drule >> strip_tac
  >- decide_tac >>
  `bt + sz <= t.vs_alloca_next` by metis_tac[alloca_next_valid_def] >>
  decide_tac
QED

Theorem ld_live_scratch_separation:
  ld_alloc_account keys d0 A s t /\ id IN keys /\
  allocas_non_overlapping t /\ alloca_next_valid t /\ allocas_from lo t /\
  lo <= t.vs_alloca_next /\ t.vs_alloca_next < dimword (:256) /\
  (id NOTIN A ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt + sz <= lo \/
    (?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME (bt,sz))) ==>
  ?p. lo <= p /\ p + 32 < dimword (:256) /\
    ((FLOOKUP t.vs_allocas id = NONE /\ p = t.vs_alloca_next) \/
      FLOOKUP t.vs_allocas id = SOME (p,32)) /\
    (!aa bb. ((aa = bb /\ aa < lo) \/ ld_site_bytes E live aa bb) ==>
      bb < p \/ p + 32 <= bb)
Proof
  strip_tac >> irule ld_live_scratch_separation_floor >>
  simp[] >> qexistsl_tac [`A`,`d0`,`keys`,`s`] >> simp[] >>
  first_assum ACCEPT_TAC
QED
