Theory lowerDloadFrameLayout
Ancestors
  lowerDloadPhaseBoundary lowerDloadFrameFloor lowerDloadLifetime
  lowerDloadPairedBoundary lowerDloadOwnership lowerDloadAllocation
  venomMemDefs venomExecSemantics finite_map pred_set

Theorem ld_local_lookup:
  (!id. ld_owned_selection E (FLOOKUP L id) (FLOOKUP H id)) /\
  ld_erase L = s.vs_allocas /\ ld_erase H = t.vs_allocas /\
  FLOOKUP L id = SOME (owner,(bs,sz)) ==>
  ?bt. ld_site_entry E owner bs bt sz /\
    FLOOKUP H id = SOME (owner,(bt,sz)) /\
    FLOOKUP s.vs_allocas id = SOME (bs,sz) /\
    FLOOKUP t.vs_allocas id = SOME (bt,sz)
Proof
  strip_tac >> first_x_assum (qspec_then `id` mp_tac) >>
  simp[ld_owned_selection_def] >> strip_tac >>
  qexists_tac `bt` >> simp[] >>
  metis_tac[ld_erase_lookup, optionTheory.OPTION_MAP_DEF, pairTheory.SND]
QED

Theorem ld_local_child_end:
  (!id. ld_owned_selection E (FLOOKUP L id) (FLOOKUP H id)) /\
  ld_erase L = s.vs_allocas /\ ld_erase H = t.vs_allocas /\
  alloca_next_valid t /\ lo <= t.vs_alloca_next /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    ((?id. FLOOKUP L id = SOME (owner,(bs,sz))) \/ bt+sz <= lo)) ==>
  !owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= t.vs_alloca_next
Proof
  rpt strip_tac >> first_x_assum drule >> disch_then drule >> strip_tac
  >- (drule_all ld_local_lookup >> strip_tac >>
      gvs[ld_site_entry_def] >> metis_tac[alloca_next_valid_def]) >>
  decide_tac
QED

(* Interface diagnostic: total paired erasures cannot contain target-only scratch. *)
Theorem ld_local_account_no_scratch:
  (!id. ld_owned_selection E (FLOOKUP L id) (FLOOKUP H id)) /\
  ld_erase L = s.vs_allocas /\ ld_erase H = t.vs_allocas /\
  ld_alloc_account keys d0 A s t ==> A = {}
Proof
  strip_tac >> drule ld_alloc_account_domain >>
  drule ld_alloc_account_disjoint >>
  simp[DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  Cases_on `x IN A` >> simp[] >>
  `x IN FDOM t.vs_allocas` by metis_tac[] >>
  `FDOM s.vs_allocas = FDOM L /\ FDOM t.vs_allocas = FDOM H` by
    metis_tac[ld_erase_def, FDOM_o_f] >>
  `x IN FDOM s.vs_allocas` by
    (qpat_x_assum `!id. ld_owned_selection _ _ _` (qspec_then `x` mp_tac) >>
     gvs[ld_owned_selection_def, FLOOKUP_DEF] >> metis_tac[]) >>
  drule ld_alloc_account_capacity >> simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_local_embedded_lookup:
  (!id. ld_owned_selection E (FLOOKUP L id) (FLOOKUP H id)) /\
  ld_erase L = s.vs_allocas /\
  (!id owner bt sz. FLOOKUP H id = SOME (owner,(bt,sz)) ==>
    FLOOKUP t.vs_allocas id = SOME (bt,sz)) /\
  FLOOKUP L id = SOME (owner,(bs,sz)) ==>
  ?bt. ld_site_entry E owner bs bt sz /\
    FLOOKUP H id = SOME (owner,(bt,sz)) /\
    FLOOKUP s.vs_allocas id = SOME (bs,sz) /\
    FLOOKUP t.vs_allocas id = SOME (bt,sz)
Proof
  strip_tac >>
  qpat_x_assum `!id. ld_owned_selection _ _ _` (qspec_then `id` mp_tac) >>
  simp[ld_owned_selection_def] >> strip_tac >>
  qexists_tac `bt` >> simp[] >>
  metis_tac[ld_erase_lookup, optionTheory.OPTION_MAP_DEF, pairTheory.SND]
QED

Theorem ld_local_embedded_child_end:
  (!id. ld_owned_selection E (FLOOKUP L id) (FLOOKUP H id)) /\
  ld_erase L = s.vs_allocas /\
  (!id owner bt sz. FLOOKUP H id = SOME (owner,(bt,sz)) ==>
    FLOOKUP t.vs_allocas id = SOME (bt,sz)) /\
  alloca_next_valid t /\ lo <= t.vs_alloca_next /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    ((?id. FLOOKUP L id = SOME (owner,(bs,sz))) \/ bt+sz <= lo)) ==>
  !owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= t.vs_alloca_next
Proof
  rpt strip_tac >> first_x_assum drule >> disch_then drule >> strip_tac
  >- (drule_all ld_local_embedded_lookup >> strip_tac >>
      gvs[ld_site_entry_def] >> metis_tac[alloca_next_valid_def]) >>
  decide_tac
QED

Theorem ld_lookup_embedding_update:
  (!id owner bt sz. FLOOKUP H id = SOME (owner,(bt,sz)) ==>
    FLOOKUP M id = SOME (bt,sz)) /\ FLOOKUP H k = NONE ==>
  !id owner bt sz. FLOOKUP H id = SOME (owner,(bt,sz)) ==>
    FLOOKUP (M |+ (k,v)) id = SOME (bt,sz)
Proof
  rpt strip_tac >> `id <> k` by (strip_tac >> gvs[]) >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ld_embedded_frame_restore:
  (ld_erase L = (merge_callee_state s sc).vs_allocas /\
   (!id owner bt sz. FLOOKUP H id = SOME (owner,(bt,sz)) ==>
     FLOOKUP (merge_callee_state t tc).vs_allocas id = SOME (bt,sz))) <=>
  (ld_erase L = s.vs_allocas /\
   (!id owner bt sz. FLOOKUP H id = SOME (owner,(bt,sz)) ==>
     FLOOKUP t.vs_allocas id = SOME (bt,sz)))
Proof
  simp[merge_callee_state_def]
QED

(* A concrete scratch-bearing frame: ordinary selections are empty, but the
   actual target map and the account both contain a real 32-byte scratch site. *)
Theorem ld_embedded_scratch_probe:
  !s k b E.
  let src = s with <| vs_allocas := FEMPTY; vs_alloca_next := b |> in
  let tgt = s with <| vs_allocas := FEMPTY |+ (k,(b,32));
                     vs_alloca_next := b+32 |> in
    ld_alloc_account {k} 0 {k} src tgt /\ {k} <> {} /\
    (!id. ld_owned_selection E (FLOOKUP FEMPTY id) (FLOOKUP FEMPTY id)) /\
    ld_erase FEMPTY = src.vs_allocas /\
    (!id owner bt sz. FLOOKUP FEMPTY id = SOME (owner,(bt,sz)) ==>
      FLOOKUP tgt.vs_allocas id = SOME (bt,sz)) /\
    FLOOKUP tgt.vs_allocas k = SOME (b,32)
Proof
  simp[ld_alloc_account_def, ld_owned_selection_def, ld_erase_def,
       FLOOKUP_UPDATE]
QED
