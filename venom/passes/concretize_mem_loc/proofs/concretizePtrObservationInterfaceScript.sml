Theory concretizePtrObservationInterface
Ancestors
  concretizePtrHistoryCoverage concretizePtrStageBounds
  concretizePtrComparisonTransport ptrDiscipline unitMemInv
  concretizePtrPairedFields concretizePtrOwnershipErasure
  concretizePtrOpaqueRetpc concretizePtrValueTransport concretizePtrMloadEndpoint
  pointerConfinedDefs memLocDefs concretizeStepStructure
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrAllocationSize
  concretizePtrParamSupport concretizePtrPairedPrefix
  concretizePtrSharedFields venomWf unitShapeDefs passSimulationDefs
  concretizePtrPrefixLedger o1PassContract venomExecProofs
  venomInst venomExecSemantics contextCodegenRel unitLabelMapIdentity
  list finite_map words arithmetic

(* access_ok retains ownership even when a provenance-bearing range lies
   numerically below lo. The absent-provenance alternative is explicit. *)
Theorem ptr_access_range_classification:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  ((ranges = source_memory_read_ranges inst s /\ mops = mem_read_ops inst) \/
   (ranges = source_memory_write_ranges inst s /\ mops = mem_write_ops inst)) /\
  MEM (off,len) ranges ==>
  len = 0 \/
  (off + len <= lo /\
    ~(?ops. mops = SOME ops /\ op_prov G ops.iao_ofst <> NONE)) \/
  (?ops v b sz. mops = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= off /\ off + len <= b + sz)
Proof
  rw[access_ok_def] >>
  Cases_on `len = 0` >> simp[] >>
  Cases_on `off + len <= lo` >>
  Cases_on `?ops. mops = SOME ops /\ op_prov G ops.iao_ofst <> NONE` >>
  gvs[] >> metis_tac[NOT_LESS_EQUAL]
QED

(* Uses the exact owned word equation; strict placement endpoint supplies
   the nonwrap condition. No target access bound is assumed. *)
Theorem ptr_owned_range_relocation_probe:
  (y:bytes32) = x - n2w b + n2w p /\
  b <= w2n x /\ w2n x + len <= b + sz /\
  p + sz < dimword(:256) ==>
  p <= w2n y /\ w2n y + len <= p + sz
Proof
  strip_tac >>
  `w2n x <= b + sz` by decide_tac >>
  drule_all ptr_closed_relocation_value >> strip_tac >> decide_tac
QED

(* Candidate ONLY: parsed and typechecked, not proved by the local probes. *)
val observation_range_transport_schema = ``
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  ptr_stage_placements Ct positions /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  in_revert_forward at.po_fn at.po_state \/
  (!off len.
    MEM (off,len) (source_memory_read_ranges at.po_inst at.po_state ++
                  source_memory_write_ranges at.po_inst at.po_state) ==>
    len = 0 \/ off + len <= lo \/
    (?aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) /\
      p <= off /\ off + len <= p + sz))
``;

Theorem ptr_terminal_length_prov:
  ptr_use_ok P pv inst /\ FDOM G SUBSET pv /\
  (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
  inst.inst_operands = [addr;lenop] ==>
  op_prov G lenop = NONE
Proof
  strip_tac >> Cases_on `lenop` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v = NONE` >>
  Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN FDOM G` by fs[FLOOKUP_DEF] >>
  `v IN pv` by fs[pred_setTheory.SUBSET_DEF] >>
  qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
  simp[ptr_use_ok_def, is_pointer_preserving_op_def,
       mem_read_ops_def, mem_write_ops_def] >>
  qexists_tac `v` >> Cases_on `addr = Var v` >> gvs[]
QED

Theorem ptr_terminal_length_taint:
  taint_ok fn tn inst s /\
  (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
  inst.inst_operands = [addr;lenop] ==>
  op_taint tn lenop = {}
Proof
  strip_tac >> gvs[taint_ok_def] >>
  first_x_assum (qspec_then `lenop` mp_tac) >> simp[]
QED

Theorem ptr_terminal_repeated_operand_probe:
  ~ptr_use_ok P {"p"}
    <|inst_id := 1; inst_opcode := RETURN;
      inst_operands := [Var "p"; Var "p"]; inst_outputs := []|> /\
  ~ptr_use_ok P {"p"}
    <|inst_id := 1; inst_opcode := REVERT;
      inst_operands := [Var "p"; Var "p"]; inst_outputs := []|>
Proof
  simp[ptr_use_ok_def, is_pointer_preserving_op_def,
       mem_read_ops_def, mem_write_ops_def] >>
  conj_tac >> qexists_tac `"p"` >> simp[]
QED

Theorem ptr_mixed_scalar_eval:
  ptr_ledger_erases births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\
  ptr_nonopaque_operand f op /\ s.vs_labels = t.vs_labels /\
  op_prov G op = NONE /\ op_taint tn op = {} ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  drule ptr_owner_op_projection >>
  disch_then (qspec_then `op` strip_assume_tac) >>
  `op_prov TG op = NONE` by
    (Cases_on `op_prov TG op` >> gvs[ptr_owner_project_def, FLOOKUP_DEF]) >>
  drule_all ptr_mixed_vars_eval >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >>
  simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]
QED

Theorem ptr_terminal_read_range_transport:
  ptr_ledger_erases births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\ ptr_use_ok P pv inst /\
  FDOM G SUBSET pv /\ taint_ok f tn inst s /\
  ptr_nonopaque_operand f addr /\ ptr_nonopaque_operand f lenop /\
  inst.inst_operands = [addr;lenop] /\
  (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
  MEM (off,len) (source_memory_read_ranges inst t) ==>
  ?x y n. eval_operand addr s = SOME x /\
    eval_operand addr t = SOME y /\
    eval_operand lenop s = SOME n /\ eval_operand lenop t = SOME n /\
    off = w2n y /\ len = w2n n /\
    MEM (w2n x,len) (source_memory_read_ranges inst s) /\
    ptr_lookup_transport births positions (op_prov TG addr) {}
      (SOME x) (SOME y)
Proof
  strip_tac >>
  `op_prov G lenop = NONE` by metis_tac[ptr_terminal_length_prov] >>
  `op_taint tn lenop = {}` by metis_tac[ptr_terminal_length_taint] >>
  `eval_operand lenop s = eval_operand lenop t` by
    (irule ptr_mixed_scalar_eval >> metis_tac[]) >>
  `op_taint tn addr = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def] >> strip_tac >>
     first_x_assum (qspec_then `addr` mp_tac) >> simp[]) >>
  `ptr_lookup_transport births positions (op_prov TG addr) {}
     (eval_operand addr s) (eval_operand addr t)` by
    (qpat_x_assum `ptr_nonopaque_operand f lenop` kall_tac >>
     drule_all ptr_mixed_vars_eval >> simp[]) >>
  gvs[contextCodegenRelTheory.source_memory_read_ranges_def,
      contextCodegenRelTheory.memory_range_of_operands_def,
      AllCaseEqs()] >>
  Cases_on `eval_operand addr t` >>
  Cases_on `eval_operand lenop t` >>
  Cases_on `eval_operand addr s` >>
  gvs[ptr_lookup_transport_def]
QED

Theorem ptr_paired_current_range_static_bound:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  ~in_revert_forward a.po_fn a.po_state /\
  ((mem_read_ops a.po_inst = SOME ops /\
    MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state)) \/
   (mem_write_ops a.po_inst = SOME ops /\
    MEM (w2n x,n) (source_memory_write_ranges a.po_inst a.po_state))) /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  n = 0 \/ w2n y + n <= eom
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `n = 0` >- simp[] >>
  drule_all ptr_paired_current_range_classification >> strip_tac
  >- (drule_all ptr_stage_fixed_region_bound >> simp[]) >>
  `ptr_stage_placements C' positions` by
    fs[concretizePtrPairedPrefixTheory.ptr_paired_prefix_def] >>
  drule_all ptr_stage_placements_endpoint_bound >> simp[] >> decide_tac
QED

Theorem ptr_paired_read_range_static_bound:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  ~in_revert_forward a.po_fn a.po_state /\
  mem_read_ops a.po_inst = SOME ops /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  n = 0 \/ w2n y + n <= eom
Proof
  strip_tac >> irule ptr_paired_current_range_static_bound >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_paired_terminal_static_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  ptr_stage_placements Ct positions /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ~in_revert_forward a.po_fn a.po_state /\
  (a.po_inst.inst_opcode = RETURN \/ a.po_inst.inst_opcode = REVERT) ==>
  !off len. MEM (off,len)
    (source_memory_read_ranges at.po_inst at.po_state ++
     source_memory_write_ranges at.po_inst at.po_state) ==>
    len = 0 \/ off + len <= eom
Proof
  strip_tac >>
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `inst_wf a.po_inst /\ fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  `?addr lenop. a.po_inst.inst_operands = [addr;lenop]` by
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[fn_shape_ok_def]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >>
     metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  suspend "terminal_operands"
QED

Resume ptr_paired_terminal_static_bound[terminal_operands]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  qpat_assum `ptr_discipline _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, pred_setTheory.SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `ptr_nonopaque_operand a.po_fn addr /\ ptr_nonopaque_operand a.po_fn lenop` by
    (qpat_x_assum `EVERY (ptr_nonopaque_operand _) _` mp_tac >> simp[]) >>
  rpt gen_tac >>
  `source_memory_write_ranges at.po_inst at.po_state = []` by
    gvs[codegenRelTheory.source_memory_write_ranges_def] >>
  simp[] >> strip_tac >>
  drule ptr_terminal_read_range_transport >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`off`, `lenop`, `len`, `addr`] mp_tac) >>
  simp[] >> strip_tac >>
  `mem_read_ops a.po_inst = SOME
    <|iao_ofst := addr; iao_size := SOME lenop; iao_max_size := SOME lenop|>` by
    simp[mem_read_ops_def] >>
  drule_at (Pat `mem_read_ops _ = _`) ptr_paired_read_range_static_bound >>
  disch_then (drule_all o SRULE []) >> simp[]
QED

Finalise ptr_paired_terminal_static_bound
