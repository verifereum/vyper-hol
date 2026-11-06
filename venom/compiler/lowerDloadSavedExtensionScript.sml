Theory lowerDloadSavedExtension
Ancestors
  lowerDloadFrameCertificate lowerDloadLifetime lowerDloadPairedBoundary
  lowerDloadOwnership finite_map pred_set list

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
