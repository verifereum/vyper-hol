Theory concretizePtrHistoricalWriteClassification
Ancestors concretizePtrHistoricalPlacement concretizePtrPlacementBounds
  concretizePtrWriteClassification concretizePtrSourceOwnership
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrPrefixLedger ptrDiscipline venomInst memLocDefs finite_map words list

Theorem ptr_historical_mcopy_write_classification:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ptr_stage_placements C' positions /\
  ptr_structural_transcript R vs C Ct h a ht at done tokens registry births PT TG saved entries H /\
  j < LENGTH h /\ EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  (EL j h).po_inst.inst_opcode = MCOPY /\
  (EL j h).po_inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop (EL j h).po_state = SOME d /\
  eval_operand sop (EL j h).po_state = SOME r /\
  eval_operand nop (EL j h).po_state = SOME n /\
  access_ok lo (EL j h).po_prov fn (EL j h).po_inst (EL j h).po_state /\
  taint_ok fn (EL j h).po_taint (EL j h).po_inst (EL j h).po_state /\
  ~in_revert_forward fn (EL j h).po_state /\ w2n n <> 0 ==>
  (op_prov TGj dop = NONE /\ op_taint (EL j h).po_taint dop = {} /\
    w2n d + w2n n <= lo) \/
  (?dv token bid db sb pb. dop = Var dv /\ FLOOKUP TGj dv = SOME (token,bid) /\
    FLOOKUP (EL j h).po_prov dv = SOME (db,sb) /\
    FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\
    db <= w2n d /\ w2n d + w2n n <= db+sb /\ pb+sb < dimword(:256))
Proof
  strip_tac >>
  `MEM (w2n d,w2n n) (source_memory_write_ranges (EL j h).po_inst (EL j h).po_state)` by
    (simp[ptr_source_write_classification, ptr_classified_write_range_def] >> metis_tac[]) >>
  `op_taint (EL j h).po_taint dop = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  drule ptr_structural_transcript_ownership >> disch_then (qspec_then `j` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  Cases_on `op_prov (EL j h).po_prov dop = NONE /\ w2n d + w2n n <= lo`
  >- (disj1_tac >> simp[] >>
      Cases_on `dop` >> gvs[op_prov_def] >>
      fs[ptr_ledger_erases_def] >>
      Cases_on `FLOOKUP TGj s` >> gvs[] >>
      metis_tac[flookup_thm]) >>
  disj2_tac >>
  qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
  simp[access_ok_def] >> strip_tac >>
  qpat_x_assum `!off len. MEM _ (source_memory_write_ranges _ _) /\ _ ==> _`
    (qspecl_then [`w2n d`,`w2n n`] mp_tac) >>
  simp[mem_write_ops_def] >>
  (impl_tac >- (strip_tac >> gvs[] >> decide_tac)) >> strip_tac >>
  rename1 `FLOOKUP (EL j h).po_prov dv = SOME (db,sb)` >>
  `?token bid. FLOOKUP TGj dv = SOME (token,bid)` by
    (fs[ptr_ledger_erases_def] >>
     Cases_on `FLOOKUP TGj dv` >> gvs[] >> PairCases_on `x` >> metis_tac[]) >>
  `?pb.
    FLOOKUP positions (Allocation bid) = SOME (pb,sb)` by
    (`j <= j` by simp[] >>
     drule_all ptr_transcript_historical_placement >> metis_tac[]) >>
  drule_all ptr_stage_placements_strict_bound >> strip_tac >>
  metis_tac[]
QED
