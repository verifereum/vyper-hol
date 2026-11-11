(* Physical interval projections of the live selected allocation map. *)
Theory lowerDloadSafetyAllocBounds
Ancestors
  lowerDloadSafetyValues lowerDloadSafetyRelation finite_map list pred_set

Theorem ld_alloc_bounds:
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\ FLOOKUP A k = SOME (b,c,n) ==>
  lo <= b /\ lo <= c
Proof
  strip_tac >> drule_all ld_slot_source_site >> strip_tac >>
  `ld_maps A (EL j frames)` by gvs[EVERY_EL] >>
  `FLOOKUP (EL j frames).lf_src.vs_allocas aid = SOME (b,n)` by
    gvs[ld_sites_def] >>
  `FLOOKUP (EL j frames).lf_tgt.vs_allocas aid = SOME (c,n)` by
    (gvs[ld_maps_def] >>
     qpat_x_assum `!aid b n. FLOOKUP _ aid = SOME (b,n) ==> ?c. _ /\ _` drule >> strip_tac >> gvs[]) >>
  `(j,aid,c,n) IN ld_sites frames F` by
    (simp[ld_sites_def] >> metis_tac[]) >>
  metis_tac[ld_global_bounds]
QED

Theorem ld_alloc_separate:
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  FLOOKUP A k = SOME (b,c,n) /\ FLOOKUP A k' = SOME (b',c',n') /\
  k <> k' /\ 0 < n /\ 0 < n' ==>
  (b+n <= b' \/ b'+n' <= b) /\ (c+n <= c' \/ c'+n' <= c)
Proof
  strip_tac >>
  `?j aid. j < LENGTH frames /\ k' = ((EL j frames).lf_serial,aid) /\
    (j,aid,b',n') IN ld_sites frames T` by
    (irule ld_slot_source_site >> simp[] >> metis_tac[]) >>
  `?j' aid'. j' < LENGTH frames /\ k = ((EL j' frames).lf_serial,aid') /\
    (j',aid',b,n) IN ld_sites frames T` by
    (irule ld_slot_source_site >> simp[] >> metis_tac[]) >>
  `ld_maps A (EL j frames) /\ ld_maps A (EL j' frames)` by gvs[EVERY_EL] >>
  `(j,aid) <> (j',aid')` by (strip_tac >> gvs[]) >>
  `FLOOKUP (EL j frames).lf_src.vs_allocas aid = SOME (b',n') /\
   FLOOKUP (EL j' frames).lf_src.vs_allocas aid' = SOME (b,n)` by
    gvs[ld_sites_def] >>
  `FLOOKUP (EL j frames).lf_tgt.vs_allocas aid = SOME (c',n') /\
   FLOOKUP (EL j' frames).lf_tgt.vs_allocas aid' = SOME (c,n)` by
    (gvs[ld_maps_def] >>
     ntac 2 (qpat_x_assum `!aid b n. FLOOKUP _ aid = SOME (b,n) ==> ?c. _ /\ _` drule >> strip_tac >> gvs[])) >>
  `(j,aid,c',n') IN ld_sites frames F /\
   (j',aid',c,n) IN ld_sites frames F` by
    (simp[ld_sites_def] >> metis_tac[]) >>
  metis_tac[ld_global_separate]
QED
