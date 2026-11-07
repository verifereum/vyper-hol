Theory concretizePtrHistoricalMcopyExclusion
Ancestors concretizePtrDemandWriteExclusion
  concretizePtrHistoricalWriteClassification concretizePtrMcopySource
  concretizePtrWritePurity concretizePtrValueTransport
  concretizePtrChronologicalHistory concretizePtrWriteClassification
  concretizePtrStructuralTranscript ptrDiscipline memLocDefs codegenRel
  venomExecSemantics venomInst finite_map list words

Theorem ptr_demand_mcopy_write_exclusion:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ w < j /\ j+1 < LENGTH h /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  fixed_region_reserved lo C /\
  ptr_vars_transport bj positions TGj (EL j h).po_taint (EL j h).po_state tgt /\
  (EL j h).po_state.vs_labels = tgt.vs_labels /\
  (EL j h).po_inst.inst_opcode = MCOPY /\
  (EL j h).po_inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop tgt = SOME dt /\ eval_operand sop tgt = SOME rt /\
  eval_operand nop tgt = SOME (n_target:bytes32) /\
  ((?u. dop = Var u) \/ (?y. dop = Lit y)) /\
  ((?u. nop = Var u) \/ (?y. nop = Lit y)) /\
  taint_ok (EL j h).po_fn (EL j h).po_taint (EL j h).po_inst (EL j h).po_state /\
  fn_ptr_ok P (EL j h).po_fn /\
  MEM (EL j h).po_inst (fn_insts (EL j h).po_fn) /\
  (!u. u IN FDOM TGj ==> u IN fn_pv P (EL j h).po_fn) ==>
  pa+k NOTIN range_bytes (step_writes (EL j h).po_inst tgt postt)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_mcopy_source_success >>
  disch_then (qspecl_then [`0`,`C`] mp_tac) >>
  disch_then (qx_choose_then `ds` (qx_choose_then `rs`
    (qx_choose_then `ns` strip_assume_tac))) >>
  `mem_write_ops (EL j h).po_inst = SOME
    <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>` by
    simp[mem_write_ops_def] >>
  `op_taint (EL j h).po_taint nop = {}` by
    (drule ptr_write_max_size_untainted >> simp[] >>
     disch_then drule >> simp[]) >>
  `op_prov TGj nop = NONE` by
    (drule ptr_write_max_size_no_provenance >> simp[] >>
     disch_then drule >> simp[]) >>
  `ns = n_target` by
    (qpat_x_assum `ptr_value_transport _ _ _ _ ns _` mp_tac >>
     simp[ptr_value_transport_scalar_empty]) >>
  qpat_x_assum `ns = n_target` SUBST_ALL_TAC >>
  Cases_on `w2n n_target = 0`
  >- simp[ptr_step_write_range, source_memory_write_ranges_def,
          sized_source_write_range_def] >>
  `j < LENGTH h /\ w <= j` by decide_tac >>
  `access_ok lo (EL j h).po_prov (EL j h).po_fn
      (EL j h).po_inst (EL j h).po_state /\
   ~in_revert_forward (EL j h).po_fn (EL j h).po_state` by
    (fs[ptr_demand_interval_def] >>
     metis_tac[rich_listTheory.EL_MEM]) >>
  `ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry births
     PT TG saved entries H /\
   ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
     (o1_walk_view rpolicy 2) C C' /\
   EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
   ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
   o1_run_state_ok vs /\ ~ctx_has_dalloca C` by
    fs[ptr_demand_interval_def] >>
  `MEM (w2n ds,w2n n_target)
    (source_memory_write_ranges (EL j h).po_inst (EL j h).po_state)` by
    (simp[ptr_source_write_classification, ptr_classified_write_range_def] >> metis_tac[]) >>
  `((op_prov TGj dop = NONE /\ op_taint (EL j h).po_taint dop = {} /\
      w2n ds + w2n n_target <= lo) \/
    (?dv tokB bid db sb pb. dop = Var dv /\ FLOOKUP TGj dv = SOME (tokB,bid) /\
     FLOOKUP (EL j h).po_prov dv = SOME (db,sb) /\
     FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\
     db <= w2n ds /\ w2n ds + w2n n_target <= db+sb /\ pb+sb < dimword(:256)))` by
    (drule_at (Pat `mem_write_ops _ = SOME _`) ptr_historical_write_classification >>
     simp[] >> disch_then drule_all >> simp[]) >>
  `b+k NOTIN range_bytes (step_writes (EL j h).po_inst (EL j h).po_state
      (mcopy (w2n ds) (w2n rs) (w2n n_target) (EL j h).po_state))` by
    (`b+k NOTIN range_bytes (step_writes (EL j h).po_inst (EL j h).po_state
        (EL (SUC j) h).po_state)` by
       (fs[ptr_demand_interval_def] >> metis_tac[]) >>
     gvs[step_writes_def]) >>
  `!op. ptr_lookup_transport bj positions (op_prov TGj op)
    (op_taint (EL j h).po_taint op)
    (eval_operand op (EL j h).po_state) (eval_operand op tgt)` by
    (drule_all ptr_vars_transport_eval_all >> simp[]) >>
  `!op. IS_SOME (eval_operand op (EL j h).po_state) =
        IS_SOME (eval_operand op tgt)` by
    (gen_tac >> first_x_assum (qspec_then `op` mp_tac) >>
     Cases_on `eval_operand op (EL j h).po_state` >>
     Cases_on `eval_operand op tgt` >> simp[ptr_lookup_transport_def]) >>
  irule ptr_demand_ordinary_write_exclusion >> simp[] >>
  goal_assum (drule_at (Pat `ptr_demand_interval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EL j H = _`)) >>
  goal_assum (drule_at (Pat `src.vs_labels = tgt.vs_labels`)) >>
  goal_assum (drule_at (Pat `_ NOTIN range_bytes (step_writes _ _ _)`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty] >>
  qexists `ds` >> gvs[]
QED
