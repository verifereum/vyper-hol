Theory concretizePtrHistoricalPlacement
Ancestors
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrStagePlacements concretizePtrSourceOwnership concretizePtrPrefixLedger
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrChronologicalHistory concretizePtrOwnerPath
  o1PassContract o1ScheduleDecompHelpers venomWf venomInst ptrDiscipline
  finite_map list rich_list pair arithmetic

Theorem ptr_transcript_birth_retained:
  !j R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H
    i tsi ri bi PTi TGi si ei tsj rj bj PTj TGj sj ej key site.
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H /\
  EVERY (\fn. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  i <= j /\ j < LENGTH h /\
  EL i H = (tsi,ri,bi,PTi,TGi,si,ei) /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  FLOOKUP bi key = SOME site ==>
  FLOOKUP bj key = SOME site
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`i = 0` by decide_tac >> gvs[]) >>
  Cases_on `i = SUC j` >- gvs[] >>
  `i <= j /\ j < LENGTH h` by decide_tac >>
  qabbrev_tac `snap = EL j H` >> PairCases_on `snap` >>
  `FLOOKUP snap2 key = SOME site` by
    (first_x_assum irule >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule ptr_structural_transcript_adjacent >> disch_then (qspec_then `j` mp_tac) >>
  simp[ptr_snapshot_step_def] >> strip_tac >>
  drule ptr_structural_transcript_ownership >> disch_then (qspec_then `j` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_tagged_chrono_step_projection >> strip_tac >>
  drule_all ptr_source_birth_caches_snoc_retained >> simp[]
QED

Theorem ptr_transcript_registry_retained:
  !j R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H
    i tsi ri bi PTi TGi si ei tsj rj bj PTj TGj sj ej token owner.
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H /\
  i <= j /\ j < LENGTH h /\
  EL i H = (tsi,ri,bi,PTi,TGi,si,ei) /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  FLOOKUP ri token = SOME owner ==>
  FLOOKUP rj token = SOME owner
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`i = 0` by decide_tac >> gvs[]) >>
  Cases_on `i = SUC j` >- gvs[] >>
  `i <= j /\ j < LENGTH h` by decide_tac >>
  qabbrev_tac `snap = EL j H` >> PairCases_on `snap` >>
  `FLOOKUP snap1 token = SOME owner` by
    (first_x_assum irule >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule ptr_structural_transcript_adjacent >> disch_then (qspec_then `j` mp_tac) >>
  simp[ptr_snapshot_step_def] >> strip_tac >>
  drule ptr_structural_transcript_ownership >> disch_then (qspec_then `j` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  `token IN FDOM snap1` by
    (qpat_x_assum `FLOOKUP snap1 token = _` mp_tac >> simp[FLOOKUP_DEF] >>
     IF_CASES_TAC >> simp[]) >>
  drule_all ptr_source_activations_registry_retained >> simp[]
QED

Theorem ptr_transcript_historical_placement:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ptr_stage_placements C' positions /\
  ptr_structural_transcript R vs C Ct h a ht at done tokens registry births PT TG saved entries H /\
  i <= j /\ j < LENGTH h /\
  EL i H = (tsi,ri,bi,PTi,TGi,si,ei) /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  FLOOKUP TGi v = SOME (token,aid) /\
  FLOOKUP (EL i h).po_prov v = SOME (b,sz) ==>
  ?d owner output p.
    d <= LENGTH (EL i h).po_stack /\
    EL (LENGTH (EL i h).po_stack-d) tsi = token /\
    FLOOKUP ri token = SOME owner /\
    owner = (ptr_owner_view d (EL i h)).cf_fn /\
    FLOOKUP (ptr_owner_view d (EL i h)).cf_state.vs_allocas aid = SOME (b,sz) /\
    lookup_function owner.fn_name C'.ctx_functions = SOME output /\
    MEM (Allocation aid,p,sz) output.fn_mems_used /\
    FLOOKUP positions (Allocation aid) = SOME (p,sz) /\
    FLOOKUP bi (token,aid) = SOME (b,sz) /\
    FLOOKUP bj (token,aid) = SOME (b,sz) /\
    FLOOKUP rj token = SOME owner
Proof
  strip_tac >> `i < LENGTH h` by decide_tac >>
  drule ptr_structural_transcript_ownership >> disch_then (qspec_then `i` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  `EVERY (\fn. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `FLOOKUP bi (token,aid) = SOME (b,sz)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[ptr_ledger_erases_def] >> strip_tac >>
     qpat_x_assum `!v. FLOOKUP _ v = _` (qspec_then `v` mp_tac) >> simp[]) >>
  `FLOOKUP bj (token,aid) = SOME (b,sz)` by
    (drule_all ptr_transcript_birth_retained >> simp[]) >>
  drule_all ptr_stage_placements_live_owner >> strip_tac >>
  `FLOOKUP rj token = SOME owner` by
    (drule_all (ptr_transcript_registry_retained |> Q.SPEC `j`) >> simp[]) >>
  qexistsl [`d`,`output`,`p`] >> gvs[]
QED
