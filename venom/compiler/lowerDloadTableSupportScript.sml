Theory lowerDloadTableSupport
Ancestors
  lowerDloadAllocationOwner lowerDloadFrameRepresentation
  lowerDloadOwnership lowerDloadLifetime lowerDloadFrameCertificate
  venomExecSemantics venomState finite_map pred_set list

Theorem ld_live_saved_projection:
  MEM f astk /\
  (!g. MEM g older ==> MEM g astk) /\
  ld_live older f.lf_local f.lf_params f.lf_prov site ==>
  ld_live astk L AP AG site
Proof
  simp[ld_live_def] >> metis_tac[]
QED

Theorem ld_alloca_saved_snapshot:
  i.inst_opcode = ALLOCA /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_frame_embedding E L H s t /\
  step_inst fuelS CS i s = OK s' /\ step_inst fuelT CT i t = OK t' /\
  FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
  FLOOKUP t'.vs_allocas i.inst_id = SOME (bt,sz) /\
  MEM f astk /\ (!g. MEM g older ==> MEM g astk) /\
  (!owner b n. ld_live older f.lf_local f.lf_params f.lf_prov (owner,(b,n)) ==>
    FLOOKUP E owner = FLOOKUP E0 owner) ==>
  let E' = if FLOOKUP L i.inst_id = NONE
           then E |+ ((0,k),(bs,bt,sz)) else E in
  ?k' L' H'.
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    ld_frame_embedding E' L' H' s' t' /\
    (!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
      FLOOKUP E' owner = FLOOKUP E owner) /\
    (!owner b n. ld_live older f.lf_local f.lf_params f.lf_prov (owner,(b,n)) ==>
      FLOOKUP E' owner = FLOOKUP E0 owner)
Proof
  strip_tac >> drule_all ld_alloca_owner_extension >> simp[] >> strip_tac >>
  qexistsl [`k'`, `L'`, `H'`] >> simp[] >>
  metis_tac[ld_live_saved_projection]
QED

Theorem ld_return_pruned_snapshot:
  (!owner b n. ld_live older f.lf_local f.lf_params f.lf_prov (owner,(b,n)) ==>
    FLOOKUP E owner = FLOOKUP E0 owner) ==>
  let R = {owner | ?b n.
    ld_live older f.lf_local f.lf_params (DRESTRICT f.lf_prov keys) (owner,(b,n))} in
  !owner b n.
    ld_live older f.lf_local f.lf_params (DRESTRICT f.lf_prov keys) (owner,(b,n)) ==>
    FLOOKUP (DRESTRICT E R) owner = FLOOKUP E0 owner
Proof
  simp[] >> rpt strip_tac >>
  `ld_live older f.lf_local f.lf_params f.lf_prov (owner,(b,n))` by
    metis_tac[ld_live_restrict_shape] >>
  simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_return_pruned_entries:
  (!owner b n. ld_live older f.lf_local f.lf_params f.lf_prov (owner,(b,n)) ==>
    FLOOKUP E owner = FLOOKUP E0 owner) ==>
  let R = {owner | ?b n.
    ld_live older f.lf_local f.lf_params (DRESTRICT f.lf_prov keys) (owner,(b,n))} in
  !owner bs bt sz.
    ld_live older f.lf_local f.lf_params (DRESTRICT f.lf_prov keys) (owner,(bs,sz)) /\
    ld_site_entry (DRESTRICT E R) owner bs bt sz ==>
    ld_live older f.lf_local f.lf_params f.lf_prov (owner,(bs,sz)) /\
    ld_site_entry E0 owner bs bt sz
Proof
  strip_tac >> drule ld_return_pruned_snapshot >> simp[] >> strip_tac >>
  rpt strip_tac >>
  drule ld_live_restrict_shape >> strip_tac >>
  gvs[ld_site_entry_def] >> metis_tac[]
QED
