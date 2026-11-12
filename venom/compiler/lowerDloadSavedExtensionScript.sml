Theory lowerDloadSavedExtension
Ancestors
  lowerDloadFrameCertificate lowerDloadLifetime lowerDloadPairedBoundary
  lowerDloadOwnership lowerDloadOwnerTransport finite_map pred_set list

Theorem ld_owned_selection_selected_transport[local]:
  ld_owned_selection E ps pt /\
  (!owner bs sz bt. ps = SOME(owner,(bs,sz)) /\
    ld_site_entry E owner bs bt sz ==> ld_site_entry E' owner bs bt sz) ==>
  ld_owned_selection E' ps pt
Proof
  rw[ld_owned_selection_def] >> metis_tac[]
QED

Theorem ld_owned_value_selected_transport[local]:
  ld_owned_value E ps pt Ms Mt x y /\
  (!owner bs sz bt. ps = SOME(owner,(bs,sz)) /\
    ld_site_entry E owner bs bt sz ==> ld_site_entry E' owner bs bt sz) ==>
  ld_owned_value E' ps pt Ms Mt x y
Proof
  Cases_on `ps` >> simp[ld_owned_value_def] >>
  PairCases_on `x'` >> simp[] >> metis_tac[]
QED

Theorem ld_saved_embedded_selected_transport:
  ld_saved_embedded V E keys d A f g /\
  (!owner bs sz bt.
    (MEM (SOME(owner,(bs,sz))) f.lf_params \/
     (?v. FLOOKUP f.lf_prov v = SOME(owner,(bs,sz))) \/
     (?id. FLOOKUP f.lf_local id = SOME(owner,(bs,sz)))) /\
    ld_site_entry E owner bs bt sz ==> ld_site_entry E' owner bs bt sz) ==>
  ld_saved_embedded V E' keys d A f g
Proof
  simp[ld_saved_embedded_def, ld_frame_embedding_def, ld_owned_vars_def] >>
  rpt strip_tac
  >- (fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
      irule ld_owned_selection_selected_transport >>
      qexists_tac `E` >> metis_tac[MEM_EL])
  >- (irule ld_owned_selection_selected_transport >>
      qexists_tac `E` >> metis_tac[])
  >- (irule ld_owned_selection_selected_transport >>
      qexists_tac `E` >> metis_tac[]) >>
  irule ld_owned_value_selected_transport >>
  qexists_tac `E` >> metis_tac[]
QED

Theorem ld_saved_embedded_owner_update:
  ld_saved_embedded V E keys d A f g /\
  (!owner bs sz.
    (MEM (SOME(owner,(bs,sz))) f.lf_params \/
     (?v. FLOOKUP f.lf_prov v = SOME(owner,(bs,sz))) \/
     (?id. FLOOKUP f.lf_local id = SOME(owner,(bs,sz)))) ==>
    owner <> owner0) ==>
  ld_saved_embedded V (E |+ (owner0,entry)) keys d A f g
Proof
  strip_tac >> irule ld_saved_embedded_selected_transport >>
  qexists_tac `E` >> simp[ld_site_entry_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ld_saved_indexed_selected_transport:
  LENGTH astk = LENGTH gstk /\ LENGTH supports = LENGTH astk /\
  LENGTH savedkeys = LENGTH astk /\ LENGTH suspended = LENGTH astk /\
  (!q. q < LENGTH astk ==>
    ld_saved_embedded
      {v | v IN EL q supports /\ ~retpc_var (EL q astk).lf_fn v}
      E (EL q savedkeys)
      (32 * SUM (MAP CARD (DROP (SUC q) suspended)))
      (EL q suspended) (EL q astk) (EL q gstk) /\
    (!v. v IN EL q supports ==>
      (lookup_var v (EL q astk).lf_state = NONE <=>
       lookup_var v (EL q gstk).lf_state = NONE)) /\
    (!v. (case FLOOKUP (EL q astk).lf_tvar v of NONE => {} | SOME m => m)
      SUBSET count 32) /\
    (!v. (case FLOOKUP (EL q gstk).lf_tvar v of NONE => {} | SOME m => m)
      SUBSET count 32)) /\
  (!q owner bs sz bt. q < LENGTH astk /\
    (MEM (SOME(owner,(bs,sz))) (EL q astk).lf_params \/
     (?v. FLOOKUP (EL q astk).lf_prov v = SOME(owner,(bs,sz))) \/
     (?id. FLOOKUP (EL q astk).lf_local id = SOME(owner,(bs,sz)))) /\
    ld_site_entry E owner bs bt sz ==> ld_site_entry E' owner bs bt sz) ==>
  LENGTH astk = LENGTH gstk /\ LENGTH supports = LENGTH astk /\
  LENGTH savedkeys = LENGTH astk /\ LENGTH suspended = LENGTH astk /\
  (!q. q < LENGTH astk ==>
    ld_saved_embedded
      {v | v IN EL q supports /\ ~retpc_var (EL q astk).lf_fn v}
      E' (EL q savedkeys)
      (32 * SUM (MAP CARD (DROP (SUC q) suspended)))
      (EL q suspended) (EL q astk) (EL q gstk) /\
    (!v. v IN EL q supports ==>
      (lookup_var v (EL q astk).lf_state = NONE <=>
       lookup_var v (EL q gstk).lf_state = NONE)) /\
    (!v. (case FLOOKUP (EL q astk).lf_tvar v of NONE => {} | SOME m => m)
      SUBSET count 32) /\
    (!v. (case FLOOKUP (EL q gstk).lf_tvar v of NONE => {} | SOME m => m)
      SUBSET count 32))
Proof
  strip_tac >> simp[] >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `q` strip_assume_tac) >> simp[] >>
  irule ld_saved_embedded_selected_transport >> qexists_tac `E` >>
  simp[] >> metis_tac[]
QED

Theorem ld_reachable_saved_indexed_owner_update:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  LENGTH astk = LENGTH gstk /\ LENGTH supports = LENGTH astk /\
  LENGTH savedkeys = LENGTH astk /\ LENGTH suspended = LENGTH astk /\
  (!q. q < LENGTH astk ==>
    ld_saved_embedded
      {v | v IN EL q supports /\ ~retpc_var (EL q astk).lf_fn v}
      E (EL q savedkeys)
      (32 * SUM (MAP CARD (DROP (SUC q) suspended)))
      (EL q suspended) (EL q astk) (EL q gstk) /\
    (!v. v IN EL q supports ==>
      (lookup_var v (EL q astk).lf_state = NONE <=>
       lookup_var v (EL q gstk).lf_state = NONE)) /\
    (!v. (case FLOOKUP (EL q astk).lf_tvar v of NONE => {} | SOME m => m)
      SUBSET count 32) /\
    (!v. (case FLOOKUP (EL q gstk).lf_tvar v of NONE => {} | SOME m => m)
      SUBSET count 32)) ==>
  LENGTH astk = LENGTH gstk /\ LENGTH supports = LENGTH astk /\
  LENGTH savedkeys = LENGTH astk /\ LENGTH suspended = LENGTH astk /\
  (!q. q < LENGTH astk ==>
    ld_saved_embedded
      {v | v IN EL q supports /\ ~retpc_var (EL q astk).lf_fn v}
      (E |+ ((0,k),entry)) (EL q savedkeys)
      (32 * SUM (MAP CARD (DROP (SUC q) suspended)))
      (EL q suspended) (EL q astk) (EL q gstk) /\
    (!v. v IN EL q supports ==>
      (lookup_var v (EL q astk).lf_state = NONE <=>
       lookup_var v (EL q gstk).lf_state = NONE)) /\
    (!v. (case FLOOKUP (EL q astk).lf_tvar v of NONE => {} | SOME m => m)
      SUBSET count 32) /\
    (!v. (case FLOOKUP (EL q gstk).lf_tvar v of NONE => {} | SOME m => m)
      SUBSET count 32))
Proof
  strip_tac >> irule ld_saved_indexed_selected_transport >>
  simp[] >> qexists_tac `E` >> simp[] >> rpt strip_tac >>
  `MEM (EL q astk) astk` by metis_tac[MEM_EL] >>
  `ld_live astk L AP AG (owner,(bs,sz))` by
    (simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  drule_all ld_annotated_serial >> simp[] >> strip_tac >>
  `owner <> (0,k)` by (strip_tac >> gvs[]) >>
  simp[ld_site_entry_def, FLOOKUP_UPDATE] >>
  gvs[ld_site_entry_def]
QED

Theorem ld_reachable_saved_param_owner_update:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  MEM sf astk /\ z < LENGTH sf.lf_params /\
  ld_owned_value E (EL z sf.lf_params) pt Ms Mt x y ==>
  ld_owned_value (E |+ ((0,k),entry)) (EL z sf.lf_params) pt Ms Mt x y
Proof
  strip_tac >> irule ld_owned_value_support >> qexists_tac `E` >>
  simp[] >> rpt strip_tac >>
  `MEM (SOME(owner,(bs,sz))) sf.lf_params` by metis_tac[MEM_EL] >>
  `ld_live astk L AP AG (owner,(bs,sz))` by
    (simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  drule_all ld_annotated_serial >> simp[] >> strip_tac >>
  `owner <> (0,k)` by (strip_tac >> gvs[]) >>
  simp[FLOOKUP_UPDATE]
QED
