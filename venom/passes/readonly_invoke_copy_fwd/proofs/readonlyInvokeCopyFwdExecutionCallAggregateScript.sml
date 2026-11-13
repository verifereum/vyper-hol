(* Actual selected source calls choose their callee translations and values. *)
Theory readonlyInvokeCopyFwdExecutionCallAggregate
Ancestors
  readonlyInvokeCopyFwdExecutionCallArgs readonlyInvokeCopyFwdExecutionCallSites
  readonlyInvokeCopyFwdExecutionCallMap readonlyInvokeCopyFwdExecutionCallValues
  readonlyInvokeCopyFwdExecutionCallIndex readonlyInvokeCopyFwdExecutionShape
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdExecutionCoverage
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdHistoryOperandOrigins readonlyInvokeCopyFwdHistoryClosure
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryVisitAccess readonlyInvokeCopyFwdHistoryCallPositions
  readonlyInvokeCopyFwdProtectionOrigin readonlyInvokeCopyFwdProtection
  readonlyInvokeCopyFwdProtectionLifetime readonlyInvokeCopyFwdLiveCertificates
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdReadonlyPositions readonlyInvokeCopyFwdHistory
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs occurrenceGeometry occurrenceOrigin
  o1LowerDloadOccurrence ptrDiscipline contextCodegenRel venomWf venomWfProps
  venomExecSemantics venomExecProofs venomState venomInst
  list rich_list finite_map pred_set words arithmetic

Theorem ricf_call_selected_filter_member[local]:
  MEM p (MAP FST (FILTER (\entry.
    SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
    ricf_selected_position (FST entry).rpe_event (FST entry).rpe_block s.vs_inst_idx)
    history)) <=>
  MEM (p,[]) history /\ s.vs_current_bb = p.rpe_block.bb_label /\
  ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx
Proof
  simp[MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem ricf_call_selected_payload_domain[local]:
  !ps. MEM p ps ==>
    (p.rpe_db,p.rpe_size) IN
      FDOM (FOLDR (\q m.
        m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps)
Proof
  Induct >> simp[FDOM_FUPDATE] >> metis_tac[]
QED

(* A current support key which is actually passed identifies a selected copy
   in this call's block, and coverage supplies its live payload. *)
Theorem ricf_call_passed_support_mapped:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_history_origin vs C ctx0 log witness ostk OPG OG OT /\
  ricf_copy_coverage ctx0 fn log a history s /\
  ricf_certificate_coverage s history certificates /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ wf_function fn /\ fn_inst_wf fn /\
  fn_inst_ids_distinct fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  witness.rpe_fn = fn /\ witness.rpe_owner = a /\
  FLOOKUP B witness.rpe_dst = SOME (witness.rpe_db,witness.rpe_size) /\
  0 < witness.rpe_size /\
  cb < LENGTH fn.fn_blocks /\
  s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions /\
  inst.inst_opcode = INVOKE /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks) /\
  j < LENGTH inst.inst_operands /\
  op_prov G (EL j inst.inst_operands) =
    SOME (witness.rpe_db,witness.rpe_size) ==>
  (witness.rpe_db,witness.rpe_size) IN
    FDOM (FOLDR (\q m.
      m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites
      (MAP FST (FILTER (\entry.
        SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
        ricf_selected_position (FST entry).rpe_event
          (FST entry).rpe_block s.vs_inst_idx) history)))
Proof
  strip_tac >>
  drule_all ricf_call_current_payload_operand_origin >> strip_tac >>
  rename1 `EL j inst.inst_operands = Var dv` >>
  `MEM (EL s.vs_inst_idx (EL cb round.fn_blocks).bb_instructions,j)
    witness.rpe_event.rfe_sites` by
    (irule ricf_call_original_alias_selected_site >> metis_tac[]) >>
  drule ricf_located_event_validation >> strip_tac >>
  `ricf_function_edit fn round` by metis_tac[ricf_function_trace_edit] >>
  `ricf_inst_edit inst
    (EL s.vs_inst_idx (EL cb round.fn_blocks).bb_instructions)` by
    metis_tac[ricf_call_function_position] >>
  `b = cb /\
   ricf_selected_position witness.rpe_event (EL cb fn.fn_blocks) s.vs_inst_idx /\
   witness.rpe_event.rfe_index < s.vs_inst_idx` by
    (irule ricf_call_located_same_block_selected >>
     fs[ricf_inst_edit_def] >> metis_tac[]) >>
  qpat_x_assum `b = cb` SUBST_ALL_TAC >>
  `MEM witness.rpe_block fn.fn_blocks /\
   witness.rpe_event.rfe_index < LENGTH witness.rpe_block.bb_instructions /\
   (ricf_event_copy witness.rpe_event witness.rpe_block).inst_opcode = MCOPY` by
    (drule_all ricf_located_event_source_block >> strip_tac >>
     drule_all ricf_located_event_source_descriptor >> strip_tac >>
     drule ricf_event_copy_shape >> strip_tac >>
     fs[ricf_block_edit_def] >> metis_tac[LIST_REL_LENGTH, EL_MEM]) >>
  `?da sa.
    MEM da (fn_insts fn) /\ da.inst_opcode = ALLOCA /\
    da.inst_outputs = [icf_assign_root (dfg_build_function fn) {} dst] /\
    da.inst_operands = [Lit sz] /\
    MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
    sa.inst_outputs = [sv] /\ sa.inst_operands = [Lit sz]` by
    (qpat_assum `ricf_history_origin vs C ctx0 log witness ostk OPG OG OT`
       (mp_then Any mp_tac ricf_history_origin_original_allocas) >>
     (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
     rule_assum_tac (PURE_REWRITE_RULE [ricf_event_copy_def]) >>
     `witness.rpe_event.rfe_index <
       LENGTH (EL cb witness.rpe_fn.fn_blocks).bb_instructions` by decide_tac >>
     drule_all ricf_source_alloca_witnesses >> strip_tac >> gvs[] >> metis_tac[]) >>
  `(ricf_event_copy witness.rpe_event witness.rpe_block).inst_operands =
    [Var dst;Var sv;Lit sz]` by metis_tac[] >>
  `witness.rpe_event.rfe_index <= s.vs_inst_idx` by decide_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME witness.rpe_block` by
    metis_tac[] >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `MEM (Var dv) inst.inst_operands` by metis_tac[EL_MEM] >>
  `?db. FLOOKUP G dv = SOME (db,w2n sz)` by
    (drule_all ricf_call_earlier_copy_values >> metis_tac[]) >>
  `FLOOKUP G dv = SOME (witness.rpe_db,witness.rpe_size)` by
    fs[op_prov_def] >>
  `w2n sz = witness.rpe_size` by
    metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  `?p ctxP logP.
    MEM (p,[]) history /\ MEM (p,[]) certificates /\
    p.rpe_event = witness.rpe_event /\ p.rpe_fn = fn /\
    p.rpe_block = EL cb fn.fn_blocks /\ p.rpe_owner = a /\
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[]) /\
    ircf_cross tn {(p.rpe_db,p.rpe_sb,p.rpe_size)} s t` by
    (mp_tac (SPEC_ALL ricf_call_selected_phase |>
       Q.INST [`e` |-> `witness.rpe_event`,`b` |-> `cb`]) >>
     (impl_tac >- (fs[ricf_event_copy_def] >> metis_tac[lookup_block_label])) >>
     simp[]) >>
  `op_prov G (Var dv) = SOME (p.rpe_db,p.rpe_size)` by
    (mp_tac (SPEC_ALL ricf_call_positive_payload_argument |>
       Q.INST [`ps` |-> `[p]`]) >>
     (impl_tac >- (fs[ricf_event_copy_def] >> metis_tac[LESS_IMP_LESS_OR_EQ])) >>
     simp[]) >>
  `(p.rpe_db,p.rpe_size) = (witness.rpe_db,witness.rpe_size)` by
    metis_tac[optionTheory.SOME_11] >>
  `(p.rpe_db,p.rpe_size) IN
    FDOM (FOLDR (\q m.
      m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites
      (MAP FST (FILTER (\entry.
        SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
        ricf_selected_position (FST entry).rpe_event
          (FST entry).rpe_block s.vs_inst_idx) history)))` by
    (irule ricf_call_selected_payload_domain >>
     simp[ricf_call_selected_filter_member] >> metis_tac[lookup_block_label]) >>
  metis_tac[]
QED

Theorem ricf_call_selected_filter_guards[local]:
  ps = MAP FST (FILTER (\entry.
    SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
    ricf_selected_position (FST entry).rpe_event (FST entry).rpe_block s.vs_inst_idx)
    history) ==>
  EVERY (\p. MEM (p,[]) history /\ s.vs_current_bb = p.rpe_block.bb_label /\
    ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx) ps
Proof
  simp[EVERY_MEM] >> metis_tac[ricf_call_selected_filter_member]
QED

Theorem ricf_call_selected_filter_certificates[local]:
  ricf_certificate_coverage s history certificates /\
  ps = MAP FST (FILTER (\entry.
    SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
    ricf_selected_position (FST entry).rpe_event (FST entry).rpe_block s.vs_inst_idx)
    history) ==>
  EVERY (\p. MEM (p,[]) certificates) ps
Proof
  strip_tac >> drule ricf_call_selected_filter_guards >>
  simp[EVERY_MEM] >> strip_tac >> rw[EVERY_MEM] >>
  rename1 `MEM p ps` >>
  `ricf_remaining_selected_use p (ricf_visit_owner_state [] s)` by
    (simp[ricf_remaining_selected_use_def, ricf_visit_owner_state_def] >>
     qexists_tac `s.vs_inst_idx` >> simp[] >> metis_tac[]) >>
  fs[ricf_certificate_coverage_def] >> metis_tac[]
QED

Theorem ricf_call_unchanged_argument_no_payload[local]:
  ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history /\
  ctx0 = icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
    (readonly_mem_analyze C) fn /\
  ricf_logged_function_trace ctx0 fn (log_of fn) last /\
  EVERY (\p. MEM (p,[]) history) ps /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  cb < LENGTH fn.fn_blocks /\
  i < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  (EL i (EL cb fn.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  j < LENGTH (EL i (EL cb fn.fn_blocks).bb_instructions).inst_operands /\
  EL j (EL i (EL cb last.fn_blocks).bb_instructions).inst_operands =
    EL j (EL i (EL cb fn.fn_blocks).bb_instructions).inst_operands ==>
  !p. MEM p ps ==>
    op_prov G (EL j (EL i (EL cb fn.fn_blocks).bb_instructions).inst_operands) <>
      SOME (p.rpe_db,p.rpe_size)
Proof
  strip_tac >> rpt strip_tac >>
  `MEM (p,[]) history` by fs[EVERY_MEM] >>
  `ricf_phase_entry vs C
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) p.rpe_fn)
    (log_of p.rpe_fn) stk PG G tn fn s a U B (p,[])` by
    (qpat_assum `ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history`
       (mp_tac o REWRITE_RULE [ricf_chosen_ledger_def, EVERY_MEM]) >>
     disch_then (qspec_then `(p,[])` mp_tac) >> simp[]) >>
  `p.rpe_fn = fn /\ p.rpe_owner = a /\
   FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\ 0 < p.rpe_size` by
    (fs[ricf_phase_entry_def] >> metis_tac[ricf_history_cursor_owner_function]) >>
  `?ostk OPG OG OT.
    ricf_history_origin vs C ctx0 (log_of fn) p ostk OPG OG OT` by
    (fs[ricf_phase_entry_def, ricf_history_cursor_def] >> metis_tac[]) >>
  drule_all ricf_call_current_payload_operand_origin >> strip_tac >>
  `(ricf_event_copy p.rpe_event (EL b fn.fn_blocks)).inst_operands =
    [Var dst;Var sv;Lit sz]` by metis_tac[] >>
  drule_all ricf_call_selected_argument_changed >> metis_tac[]
QED

Theorem ricf_call_eval_operands_indexed[local]:
  !ops s args. eval_operands ops s = SOME args ==>
  LENGTH args = LENGTH ops /\
  !j. j < LENGTH ops ==> eval_operand (EL j ops) s = SOME (EL j args)
Proof
  Induct >> simp[eval_operands_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> simp[] >> Cases >> simp[]
QED

Theorem ricf_call_argument_list[local]:
  eval_operands ops s = SOME args /\ LENGTH ops' = LENGTH ops /\
  (!j. j < LENGTH ops ==>
    ?y. eval_operand (EL j ops') t = SOME y /\
      ricf_opaque_value_agree callsites (op_prov G (EL j ops)) {} (EL j args) y) ==>
  ?args'. eval_operands ops' t = SOME args' /\
    ricf_opaque_params_agree callsites (MAP (op_prov G) ops) args args'
Proof
  strip_tac >> drule ricf_call_eval_operands_indexed >> strip_tac >>
  `IS_SOME (eval_operands ops' t)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> rpt strip_tac >>
     metis_tac[MEM_EL, optionTheory.IS_SOME_EXISTS]) >>
  `?args'. eval_operands ops' t = SOME args'` by fs[optionTheory.IS_SOME_EXISTS] >>
  drule ricf_call_eval_operands_indexed >> strip_tac >>
  qexists_tac `args'` >> simp[ricf_opaque_params_agree_def, EL_MAP] >>
  rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH ops ==> ?y. _` (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >> metis_tac[optionTheory.SOME_11]
QED
