Theory concretizePtrHistoricalWriteClassification
Ancestors concretizePtrHistoricalPlacement concretizePtrPlacementBounds
  concretizePtrWriteClassification concretizePtrSourceOwnership
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrPrefixLedger ptrDiscipline venomInst memLocDefs finite_map words list

Theorem ptr_write_offset_untainted[local]:
  taint_ok fn tn inst s /\ mem_write_ops inst = SOME ops ==>
  op_taint tn ops.iao_ofst = {}
Proof
  Cases_on `inst.inst_opcode` >> simp[mem_write_ops_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem ptr_historical_write_classification:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\
  ptr_stage_placements C' positions /\
  ptr_structural_transcript R vs C Ct h a ht at done tokens registry births PT TG saved entries H /\
  j < LENGTH h /\ EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  mem_write_ops (EL j h).po_inst = SOME ops /\
  eval_operand ops.iao_ofst (EL j h).po_state = SOME d /\
  MEM (w2n d,len) (source_memory_write_ranges (EL j h).po_inst (EL j h).po_state) /\
  access_ok lo (EL j h).po_prov fn (EL j h).po_inst (EL j h).po_state /\
  taint_ok fn (EL j h).po_taint (EL j h).po_inst (EL j h).po_state /\
  ~in_revert_forward fn (EL j h).po_state /\ len <> 0 ==>
  (op_prov TGj ops.iao_ofst = NONE /\ op_taint (EL j h).po_taint ops.iao_ofst = {} /\
    (w2n d + len <= lo \/ w2n vs.vs_initial_fmp <= w2n d)) \/
  (?dv token bid db sb pb. ops.iao_ofst = Var dv /\ FLOOKUP TGj dv = SOME (token,bid) /\
    FLOOKUP (EL j h).po_prov dv = SOME (db,sb) /\
    FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\
    db <= w2n d /\ w2n d + len <= db+sb /\ pb+sb < dimword(:256))
Proof
  cheat
QED
