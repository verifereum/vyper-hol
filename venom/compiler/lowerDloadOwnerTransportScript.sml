Theory lowerDloadOwnerTransport
Ancestors
  lowerDloadFrameCertificate lowerDloadOwnership lowerDloadLifetime
  lowerDloadPairedBoundary lowerDloadPhaseBoundary finite_map list

Theorem ld_owned_selection_support:
  ld_owned_selection E ps pt /\
  (!owner bs sz. ps = SOME (owner,(bs,sz)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  ld_owned_selection E' ps pt
Proof
  rw[ld_owned_selection_def] >>
  gvs[ld_site_entry_def] >> metis_tac[]
QED

Theorem ld_owned_value_support:
  ld_owned_value E ps pt Ms Mt x y /\
  (!owner bs sz. ps = SOME (owner,(bs,sz)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  ld_owned_value E' ps pt Ms Mt x y
Proof
  Cases_on `ps` >> simp[ld_owned_value_def] >>
  PairCases_on `x'` >> simp[ld_owned_value_def, ld_site_entry_def] >>
  metis_tac[]
QED

Theorem ld_owned_vars_support:
  ld_owned_vars V E AG AH tn un s t /\
  (!v owner bs sz. FLOOKUP AG v = SOME (owner,(bs,sz)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  ld_owned_vars V E' AG AH tn un s t
Proof
  rw[ld_owned_vars_def] >>
  irule ld_owned_value_support >> metis_tac[]
QED

Theorem ld_frame_embedding_support:
  ld_frame_embedding E L H s t /\
  (!id owner bs sz. FLOOKUP L id = SOME (owner,(bs,sz)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  ld_frame_embedding E' L H s t
Proof
  rw[ld_frame_embedding_def] >>
  irule ld_owned_selection_support >> metis_tac[]
QED

Theorem ld_owned_params_support:
  !ps pt. LIST_REL (ld_owned_selection E) ps pt /\
  (!owner bs sz. MEM (SOME (owner,(bs,sz))) ps ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  LIST_REL (ld_owned_selection E') ps pt
Proof
  Induct >> gen_tac >> Cases_on `pt` >> simp[] >> strip_tac >>
  conj_tac
  >- (irule ld_owned_selection_support >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem ld_saved_embedded_support:
  ld_saved_embedded V E keys d A f g /\
  (!owner bs sz. ld_selected f.lf_local f.lf_params f.lf_prov
    (owner,(bs,sz)) ==> FLOOKUP E' owner = FLOOKUP E owner) ==>
  ld_saved_embedded V E' keys d A f g
Proof
  simp[ld_saved_embedded_def] >> strip_tac >>
  conj_tac
  >- (irule ld_owned_params_support >>
      gvs[ld_selected_def] >> metis_tac[]) >>
  conj_tac
  >- (gen_tac >> irule ld_owned_selection_support >>
      gvs[ld_selected_def] >> metis_tac[]) >>
  conj_tac
  >- (irule ld_frame_embedding_support >>
      gvs[ld_selected_def] >> metis_tac[]) >>
  irule ld_owned_vars_support >> gvs[ld_selected_def] >> metis_tac[]
QED

Theorem ld_saved_stack_support:
  !fs gs.
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) fs gs /\
  (!f owner bs sz. MEM f fs /\
    ld_selected f.lf_local f.lf_params f.lf_prov (owner,(bs,sz)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E' keys d A f g) fs gs
Proof
  Induct >> gen_tac >> Cases_on `gs` >> simp[] >> strip_tac >>
  conj_tac
  >- (qexistsl_tac [`V`,`keys`,`d`,`A`] >>
      irule ld_saved_embedded_support >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem ld_reachable_stack_fresh_owner:
  ld_annotated_reachable vs0 C astk k L AP AG tn fn inst s /\
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) astk bstk ==>
  LIST_REL (\f g. ?V keys d A.
    ld_saved_embedded V (E |+ ((0,k),(bs,bt,sz))) keys d A f g) astk bstk
Proof
  strip_tac >> irule ld_saved_stack_support >> qexists_tac `E` >> simp[] >>
  rpt strip_tac >>
  `ld_live astk L AP AG (owner,(bs',sz'))` by
    (simp[ld_live_def] >> metis_tac[]) >>
  drule_all ld_annotated_serial >> simp[] >> strip_tac >>
  `owner <> (0,k)` by (strip_tac >> gvs[]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem ld_saved_embedded_restrict:
  ld_saved_embedded V E keys d A f g /\
  (!owner bs sz. ld_selected f.lf_local f.lf_params f.lf_prov
    (owner,(bs,sz)) ==> owner IN survivors) ==>
  ld_saved_embedded V (DRESTRICT E survivors) keys d A f g
Proof
  strip_tac >> irule ld_saved_embedded_support >> qexists_tac `E` >> simp[] >>
  rpt strip_tac >> simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_saved_stack_restrict:
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) fs gs /\
  (!f owner bs sz. MEM f fs /\
    ld_selected f.lf_local f.lf_params f.lf_prov (owner,(bs,sz)) ==>
    owner IN survivors) ==>
  LIST_REL (\f g. ?V keys d A.
    ld_saved_embedded V (DRESTRICT E survivors) keys d A f g) fs gs
Proof
  strip_tac >> irule ld_saved_stack_support >> qexists_tac `E` >> simp[] >>
  rpt strip_tac >> simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED
