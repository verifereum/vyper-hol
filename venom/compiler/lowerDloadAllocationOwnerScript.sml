Theory lowerDloadAllocationOwner
Ancestors
  lowerDloadOrdinaryAllocation lowerDloadOwnerTransport lowerDloadOwnership
  lowerDloadFrameCertificate lowerDloadPairedBoundary lowerDloadLifetime
  venomExecSemantics venomState venomInst finite_map pred_set list

Theorem ld_alloca_preserves_entry[local]:
  i.inst_opcode = ALLOCA /\ step_inst fuel C i s = OK s' /\
  FLOOKUP s.vs_allocas id = SOME p ==>
  FLOOKUP s'.vs_allocas id = SOME p
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[]
QED

Theorem ld_alloca_owner_extension:
  i.inst_opcode = ALLOCA /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_frame_embedding E L H s t /\
  step_inst fuelS CS i s = OK s' /\ step_inst fuelT CT i t = OK t' /\
  FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
  FLOOKUP t'.vs_allocas i.inst_id = SOME (bt,sz) ==>
  let E' = if FLOOKUP L i.inst_id = NONE
           then E |+ ((0,k),(bs,bt,sz)) else E in
  ?k' L' H'.
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    ld_frame_embedding E' L' H' s' t' /\
    (!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
      FLOOKUP E' owner = FLOOKUP E owner)
Proof
  strip_tac >> simp[] >>
  `!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
    FLOOKUP (E |+ ((0,k),(bs,bt,sz))) owner = FLOOKUP E owner` by
    (rpt strip_tac >> drule_all ld_annotated_serial >> simp[] >>
     strip_tac >> `owner <> (0,k)` by (strip_tac >> gvs[]) >>
     simp[FLOOKUP_UPDATE]) >>
  `ld_erase (SND (ld_select_alloca k L i s')) = s'.vs_allocas` by
    (`ld_erase L = s.vs_allocas` by metis_tac[ld_frame_embedding_source] >>
     `i.inst_opcode <> INVOKE` by simp[] >>
     drule_all ld_select_alloca_erase >> simp[]) >>
  Cases_on `FLOOKUP L i.inst_id`
  >- suspend "fresh"
  >> suspend "cached"
QED

Resume ld_alloca_owner_extension[fresh]:
  `FLOOKUP H i.inst_id = NONE` by
    (drule ld_frame_embedding_selection >>
     disch_then (qspec_then `i.inst_id` mp_tac) >>
     simp[ld_owned_selection_def]) >>
  `ld_frame_embedding (E |+ ((0,k),(bs,bt,sz))) L H s t` by
    (irule ld_frame_embedding_support >> qexists `E` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  gvs[ld_select_alloca_def] >>
  conj_tac
  >- (simp[ld_frame_embedding_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (gen_tac >> Cases_on `i.inst_id = id`
          >- simp[ld_owned_selection_def, ld_site_entry_def, FLOOKUP_UPDATE] >>
          simp[] >> metis_tac[ld_frame_embedding_selection]) >>
      rpt gen_tac >> Cases_on `i.inst_id = id` >- (strip_tac >> gvs[]) >>
      simp[] >> strip_tac >>
      `FLOOKUP t.vs_allocas id = SOME (bt',sz')` by
        metis_tac[ld_frame_embedding_target] >>
      drule_all ld_alloca_preserves_entry >> simp[]) >>
  metis_tac[]
QED

Resume ld_alloca_owner_extension[cached]:
  `FLOOKUP H i.inst_id <> NONE` by
    (drule ld_frame_embedding_selection >>
     disch_then (qspec_then `i.inst_id` mp_tac) >>
     simp[ld_owned_selection_def] >> strip_tac >> gvs[]) >>
  gvs[ld_select_alloca_def] >>
  simp[ld_frame_embedding_def] >> conj_tac
  >- metis_tac[ld_frame_embedding_selection] >>
  rpt strip_tac >>
  `FLOOKUP t.vs_allocas id = SOME (bt',sz')` by
    metis_tac[ld_frame_embedding_target] >>
  drule_all ld_alloca_preserves_entry >> simp[]
QED

Finalise ld_alloca_owner_extension
