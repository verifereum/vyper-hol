Theory lowerDloadAllocaRepresentation
Ancestors
  lowerDloadAllocationOwner lowerDloadFrameRepresentation lowerDloadOwnership
  lowerDloadLifetime lowerDloadFrameCertificate lowerDloadPairedBoundary
  venomExecSemantics venomState finite_map pred_set list

Theorem ld_alloca_live_cases[local]:
  i.inst_opcode = ALLOCA /\
  FLOOKUP s'.vs_allocas i.inst_id = SOME(bs,sz) /\
  ld_select_alloca k L i s' = (k',L') /\
  ld_live astk L' AP (ld_step_prov AP AG L' i) site ==>
  ld_live astk L AP AG site \/
  (FLOOKUP L i.inst_id = NONE /\ site = ((0,k),(bs,sz)))
Proof
  strip_tac >>
  `ld_live astk L' AP AG site` by
    (fs[ld_live_def] >> metis_tac[ld_step_selected]) >>
  qpat_x_assum `ld_live _ _ _ (ld_step_prov _ _ _ _) _` kall_tac >>
  Cases_on `FLOOKUP L i.inst_id` >>
  gvs[ld_select_alloca_def, ld_live_def, ld_selected_def, FLOOKUP_UPDATE,
      AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ld_alloca_live_representation:
  i.inst_opcode = ALLOCA /\ i.inst_id NOTIN keys /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_frame_embedding E L H s t /\
  step_inst fuelS CS i s = OK s' /\ step_inst fuelT CT i t = OK t' /\
  FLOOKUP s'.vs_allocas i.inst_id = SOME(bs,sz) /\
  FLOOKUP t'.vs_allocas i.inst_id = SOME(bt,sz) /\
  (!owner b c n. ld_live astk L AP AG (owner,(b,n)) /\
    ld_site_entry E owner b c n ==>
    c+n <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(c,n)) ==>
  let E' = if FLOOKUP L i.inst_id = NONE
           then E |+ ((0,k),(bs,bt,sz)) else E in
  ?k' L' H'.
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    ld_frame_embedding E' L' H' s' t' /\
    (!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
      FLOOKUP E' owner = FLOOKUP E owner) /\
    (!owner b c n. ld_live astk L' AP (ld_step_prov AP AG L' i) (owner,(b,n)) /\
      ld_site_entry E' owner b c n ==>
      c+n <= f \/ ?j. j NOTIN keys /\ FLOOKUP t'.vs_allocas j = SOME(c,n))
Proof
  strip_tac >> drule_all ld_alloca_owner_extension >> simp[] >> strip_tac >>
  qexistsl [`k'`, `L'`, `H'`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  drule_all ld_alloca_live_cases >> strip_tac
  >- (`ld_site_entry E owner b c n` by
        (gvs[ld_site_entry_def] >> metis_tac[]) >>
      `c+n <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(c,n)` by
        metis_tac[] >>
      metis_tac[ld_alloca_preserves_entry]) >>
  gvs[ld_site_entry_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED
