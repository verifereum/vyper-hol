(* Transport the fixed trace choice through actual source execution. *)
Theory readonlyInvokeCopyFwdExecutionHistoryLifecycle
Ancestors
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdAnalyzedLifecycle
  readonlyInvokeCopyFwdAlignedOrigins readonlyInvokeCopyFwdHeterogeneousMapOrigins
  readonlyInvokeCopyFwdLiveCertificates readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryPhaseAllocation readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdHistoryStackAlignment readonlyInvokeCopyFwdProtection
  readonlyInvokeCopyFwdHistoryRelevance readonlyInvokeCopyFwdHistoryVisitAccess
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdDefs
  readonlyInvokeCopyFwdProtectionLifetime
  venomInstProofs venomWf venomWfProps fnFrameStepsRevertForward
  readonlyInvokeCopyFwdProtectionOrigin readonlyInvokeCopyFwdHistorySelected
  frameAllocationHistory words readonlyInvokeCopyFwdHistorySize
  readonlyInvokeCopyFwdHeterogeneousLifecycle o1LowerDloadOccurrence
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs venomExecSemantics venomState venomInst
  finite_map list pred_set

Theorem ricf_chosen_ledger_next[local]:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u ==>
  ricf_chosen_ledger vs C log_of stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U (occurrence_sites_step a B inst u) history
Proof
  simp[ricf_chosen_ledger_def, EVERY_MEM] >> rpt strip_tac >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  first_x_assum drule >> strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule ricf_phase_entry_alloca >> metis_tac[]) >>
  irule ricf_phase_entry_next >> metis_tac[]
QED

Theorem ricf_chosen_ledger_call[local]:
  ricf_chosen_ledger vs C log_of stk PG G tn caller s a U B history /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 ==>
  ricf_chosen_ledger vs C log_of
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
    n (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (ricf_phase_push
      <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> history)
Proof
  simp[ricf_chosen_ledger_def, ricf_phase_push_def, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_MAP] >> rename1 `MEM entry history` >>
  Cases_on `entry` >> gvs[] >> first_x_assum drule >> strip_tac >> fs[] >>
  irule ricf_phase_entry_call >> metis_tac[]
QED

Theorem ricf_chosen_ledger_block[local]:
  ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_chosen_ledger vs C log_of stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn s1 a U B
    (FILTER (\entry. SND entry <> []) history)
Proof
  simp[ricf_chosen_ledger_def, EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> Cases_on `entry` >>
  rename1 `MEM (p,pre) history` >>
  gvs[ricf_phase_entry_def, ricf_history_cursor_def] >>
  Cases_on `pre` >> gvs[] >> metis_tac[ricf_visit_prefix_block]
QED

Theorem ricf_chosen_ledger_return[local]:
  occ_frame_reachable vs C (f::stk) PG G tn fn inst s n a (u::U) B HP H /\
  ricf_chosen_ledger vs C log_of (f::stk) PG G tn fn s a (u::U) B history /\
  active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_chosen_ledger vs C log_of stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    u.of_owner U (DRESTRICT B {id | FST id <> a}) (ricf_phase_pop history)
Proof
  strip_tac >>
  rw[ricf_chosen_ledger_def, EVERY_MEM, ricf_phase_pop_def, MEM_MAP, MEM_FILTER] >>
  rename1 `MEM entry history` >> Cases_on `entry` >> gvs[] >>
  rename1 `MEM (p,pre) history` >>
  `ricf_phase_entry vs C
     (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
       (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
     (f::stk) PG G tn fn s a (u::U) B (p,pre)` by
    (fs[ricf_chosen_ledger_def, EVERY_MEM] >>
     qpat_x_assum `!entry. MEM entry history ==> _`
       (qspec_then `(p,pre)` mp_tac) >> simp[]) >>
  `ricf_source_ledger vs C
     (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
       (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
     (f::stk) PG G tn fn inst s n a (u::U) B HP H [(p,pre)]` by
    simp[ricf_source_ledger_def] >>
  drule_all ricf_source_ledger_return >>
  simp[ricf_source_ledger_def, ricf_phase_pop_def]
QED

Theorem ricf_chosen_support_sites_step:
  ricf_chosen_support vs C log_of a fn B E /\
  occurrence_allocas_ok B a s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK u ==>
  ricf_chosen_support vs C log_of a fn (occurrence_sites_step a B inst u) E
Proof
  rw[ricf_chosen_support_def] >> first_x_assum drule >> simp[] >> strip_tac >>
  qexistsl_tac [`p`,`stk0`,`PG0`,`G0`,`tn0`] >> simp[] >>
  conj_tac >> irule occurrence_sites_step_preserves >> metis_tac[]
QED

Theorem ricf_chosen_selected_opcode[local]:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_selected_position e (EL b fn.fn_blocks) j ==>
  (EL j (EL b fn.fn_blocks).bb_instructions).inst_opcode = INVOKE
Proof
  strip_tac >> drule_all ricf_located_event_selected_position_site >> strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  `j < LENGTH (EL b fn.fn_blocks).bb_instructions` by
    (fs[ricf_selected_position_def] >> metis_tac[findi_some_index]) >>
  `(EL j (EL b round.fn_blocks).bb_instructions).inst_opcode = INVOKE` by
    metis_tac[ricf_event_sites_readonly] >>
  `ricf_function_edit fn round` by metis_tac[ricf_function_trace_edit] >>
  `ricf_block_edit (EL b fn.fn_blocks) (EL b round.fn_blocks)` by
    (fs[ricf_function_edit_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  drule ricf_block_edit_EL >> strip_tac >>
  `ricf_inst_edit (EL j (EL b fn.fn_blocks).bb_instructions)
     (EL j (EL b round.fn_blocks).bb_instructions)` by metis_tac[] >>
  qpat_x_assum `!i. _ ==> ricf_inst_edit _ _` kall_tac >>
  qpat_x_assum `ricf_inst_edit _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_inst_edit_def]) >> gvs[]
QED

Theorem ricf_certificate_owner_next[local]:
  ricf_history_cursor vs C ctx0 log p [] PG G tn fn s /\
  active_inst fn inst s /\ wf_function p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
  ricf_remaining_selected_use p s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK u /\ ~is_terminator inst.inst_opcode ==>
  ricf_remaining_selected_use p (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all ricf_history_cursor_owner_position >> strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  fs[ricf_history_cursor_def, ricf_history_origin_def,
    ricf_remaining_selected_use_def] >>
  `SUC s.vs_inst_idx <= j` by
    (`s.vs_inst_idx <> j` by
      (strip_tac >> gvs[] >> drule_all ricf_chosen_selected_opcode >> simp[]) >>
     decide_tac) >>
  qexists_tac `j` >> simp[] >> metis_tac[]
QED

Theorem ricf_certificate_live_next[local]:
  ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history /\
  ricf_certificate_coverage s history certificates /\
  ricf_certificate_live s certificates /\
  wf_function fn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK u /\ ~is_terminator inst.inst_opcode ==>
  ricf_certificate_live (u with vs_inst_idx := SUC s.vs_inst_idx) certificates
Proof
  rw[ricf_certificate_live_def, EVERY_MEM] >> rename1 `MEM entry certificates` >>
  Cases_on `entry` >> gvs[] >> rename1 `MEM (p,frames) certificates` >>
  `ricf_remaining_selected_use p (ricf_visit_owner_state frames s)` by
    (qpat_x_assum `!entry. MEM entry certificates ==> _`
       (qspec_then `(p,frames)` mp_tac) >> simp[]) >>
  Cases_on `frames = []` >> gvs[ricf_visit_owner_state_def] >>
  `MEM (p,[]) history` by fs[ricf_certificate_coverage_def, SUBSET_DEF] >>
  `ricf_history_cursor vs C
     (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
       (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn) p [] PG G tn fn s` by
    (fs[ricf_chosen_ledger_def, EVERY_MEM] >>
     qpat_x_assum `!entry. MEM entry history ==> _`
       (qspec_then `(p,[])` mp_tac) >> simp[ricf_phase_entry_def]) >>
  `fn = p.rpe_fn` by metis_tac[ricf_history_cursor_owner_function] >>
  irule ricf_certificate_owner_next >> metis_tac[]
QED

Theorem ricf_certificate_readonly_next[local]:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_certificate_readonly vs C log_of stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U (occurrence_sites_step a B inst u) certificates
Proof
  rw[ricf_certificate_readonly_def] >>
  qpat_x_assum `!p frames. _` (qspecl_then [`p`,`frames`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`inner`,`anchor`,`tail`,`atn`] >> simp[] >>
  `ricf_aligned_origin_at vs C
     (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
       (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
     stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
     (u with vs_inst_idx := SUC s.vs_inst_idx) U B
     (p.rpe_db,p.rpe_size) (p.rpe_db,p.rpe_sb,p.rpe_size)
     p inner anchor tail atn` by
    (irule ricf_aligned_origin_next >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule ricf_aligned_origin_sites_step >>
      drule occ_frame_reachable_annotation >>
      fs[occurrence_annotation_ok_def] >> metis_tac[]) >>
  fs[occurrence_sites_step_def]
QED

Theorem ricf_history_certificates_next:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B
    history certificates /\
  wf_function fn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_history_certificates vs C log_of stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U (occurrence_sites_step a B inst u) history certificates
Proof
  simp[ricf_history_certificates_def] >> strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  rpt conj_tac
  >- (irule ricf_chosen_ledger_next >> metis_tac[])
  >- (irule ricf_certificate_coverage_advance >> qexists_tac `s` >> simp[])
  >- (irule ricf_certificate_live_next >> metis_tac[]) >>
  irule ricf_certificate_readonly_next >> metis_tac[]
QED

Theorem ricf_certificate_live_push[local]:
  ricf_certificate_live s certificates /\ f.cf_state = s ==>
  ricf_certificate_live t (ricf_phase_push f certificates)
Proof
  simp[ricf_certificate_live_def, ricf_phase_push_def, EVERY_MAP,
    EVERY_MEM] >> rpt strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM entry certificates` >> Cases_on `entry` >> gvs[] >>
  rename1 `MEM (p,pre) certificates` >>
  qpat_x_assum `!entry. MEM entry certificates ==> _`
    (qspec_then `(p,pre)` mp_tac) >> simp[] >>
  metis_tac[ricf_visit_owner_state_push]
QED

Theorem ricf_certificate_readonly_block[local]:
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_certificate_readonly vs C log_of stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 U B
    (FILTER (\entry. SND entry <> []) certificates)
Proof
  rw[ricf_certificate_readonly_def, MEM_FILTER] >>
  qpat_x_assum `!p frames. _` (qspecl_then [`p`,`frames`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`inner`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_block >> metis_tac[]
QED

Theorem ricf_history_origin_size_bound[local]:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_history_origin vs C ctx0 log p stk PG G tn ==>
  p.rpe_size < dimword (:256)
Proof
  simp[ricf_history_origin_def, ricf_source_copy_payload_def] >> rpt strip_tac >>
  `occurrence_allocas_ok B p.rpe_owner p.rpe_before` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  `FLOOKUP p.rpe_before.vs_allocas (SND p.rpe_dst) =
      SOME (p.rpe_db,p.rpe_size)` by
    (fs[occurrence_allocas_ok_def] >> metis_tac[pairTheory.PAIR]) >>
  drule_all occ_frame_reachable_current_allocation_syntax >> strip_tac >>
  simp[wordsTheory.w2n_lt]
QED

Theorem ricf_history_origin_read_size[local]:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_history_origin vs C ctx0 log p stk PG G tn /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts p.rpe_fn)) /\
  ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn ==>
  ?round b es prefix current.
    ricf_located_event ctx0 p.rpe_fn log round b es prefix p.rpe_event current /\
    p.rpe_block = EL b p.rpe_fn.fn_blocks /\
    (bp_get_read_location p.rpe_event.rfe_ctx.icf_bp
      (ricf_event_copy p.rpe_event current) AddrSp_Memory).ml_size =
      SOME p.rpe_size
Proof
  strip_tac >>
  `p.rpe_size < dimword (:256)` by metis_tac[ricf_history_origin_size_bound] >>
  drule_all ricf_history_origin_original_allocas >> strip_tac >>
  fs[ricf_history_origin_def] >>
  `eval_operand (Lit sz) p.rpe_before = SOME (n2w p.rpe_size)` by
    fs[ricf_source_copy_payload_def, eval_operands_def, eval_operand_def,
       AllCaseEqs()] >>
  qpat_assum `p.rpe_block = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_all ricf_located_event_read_size >>
  simp[wordsTheory.w2n_n2w] >> strip_tac >> metis_tac[]
QED

Theorem ricf_certificate_owner_suspend[local]:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  wf_function fn /\ ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occ_frame_reachable vs C stk PG G tn fn callinst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\ occurrence_syntax_origin fn a H /\
  ricf_phase_entry vs C
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
    stk PG G tn fn s a U B (p,[]) /\
  ricf_remaining_selected_use p s /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_aligned_origin_at vs C
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
    (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (p.rpe_db,p.rpe_size) (p.rpe_db,p.rpe_sb,p.rpe_size)
    p [] (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>) stk tn
Proof
  strip_tac >> fs[ricf_phase_entry_def] >>
  `fn = p.rpe_fn` by metis_tac[ricf_history_cursor_owner_function] >> gvs[] >>
  drule_all ricf_history_cursor_owner_position >> strip_tac >>
  `?ostk OPG OG OT. ricf_history_origin vs C
     (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
       (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn) p ostk OPG OG OT` by
    (fs[ricf_history_cursor_def] >> metis_tac[]) >>
  drule_all ricf_history_origin_original_allocas >> strip_tac >>
  `dfg_get_def (dfg_build_function p.rpe_fn)
     (icf_assign_root (dfg_build_function p.rpe_fn) {} dst) = SOME da /\
   dfg_get_def (dfg_build_function p.rpe_fn) sv = SOME sa` by
    (conj_tac >> irule dfg_build_function_ssa_def >> simp[]) >>
  drule_all ricf_history_origin_read_size >> strip_tac >>
  `(bp_get_read_location p.rpe_event.rfe_ctx.icf_bp
      (ricf_event_copy p.rpe_event current) AddrSp_Memory).ml_size <> SOME 0` by
    (strip_tac >> gvs[]) >>
  drule_all ricf_history_relevant_owner_call_site >> strip_tac >>
  `s.vs_current_bb = p.rpe_block.bb_label` by fs[ricf_remaining_selected_use_def] >>
  `ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx` by
    (fs[ricf_remaining_selected_use_def] >>
     `s.vs_inst_idx = j` by
       (irule ricf_located_event_owner_call_cutoff >> metis_tac[]) >> simp[]) >>
  `occurrence_annotation_ok n p.rpe_owner U B HP H stk PG G s` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `fn_inst_ids_distinct p.rpe_fn` by fs[wf_function_def] >>
  gvs[] >>
  `FLOOKUP s.vs_allocas da.inst_id = SOME (p.rpe_db,p.rpe_size) /\
   FLOOKUP s.vs_allocas sa.inst_id = SOME (p.rpe_sb,p.rpe_size) /\
   (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_db,p.rpe_size)
        ==> rma_is_readonly (readonly_mem_analyze C) nm k) /\
   (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_sb,p.rpe_size)
        ==> EL k ops = Var sv /\ rma_is_readonly (readonly_mem_analyze C) nm k)` by
    (irule ricf_history_relevant_call_endpoints >> simp[] >>
     goal_assum (drule_at (Pat `ricf_history_cursor _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ricf_located_event _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  irule ricf_aligned_origin_selected >> simp[icf_build_ctx_def] >>
  metis_tac[occ_frame_reachable_projection, wf_function_def]
QED

Theorem ricf_certificate_readonly_call[local]:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  wf_function fn /\ ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occ_frame_reachable vs C stk PG G tn fn callinst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\ occurrence_syntax_origin fn a H /\
  ricf_history_certificates vs C log_of stk PG G tn fn callinst s a U B
    history certificates /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_certificate_readonly vs C log_of
    (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (ricf_phase_push <|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> certificates)
Proof
  strip_tac >>
  fs[ricf_history_certificates_def] >>
  rw[ricf_certificate_readonly_def, ricf_phase_push_def, MEM_MAP] >>
  rename1 `MEM entry certificates` >> Cases_on `entry` >> gvs[] >>
  rename1 `MEM (p,frames0) certificates` >>
  Cases_on `frames0 = []`
  >- (gvs[] >>
      `MEM (p,[]) history` by fs[ricf_certificate_coverage_def, SUBSET_DEF] >>
      `ricf_phase_entry vs C
         (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
           (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
         stk PG G tn fn s a U B (p,[])` by
        (fs[ricf_chosen_ledger_def, EVERY_MEM] >>
         qpat_x_assum `!entry. MEM entry history ==> _`
           (qspec_then `(p,[])` mp_tac) >> simp[]) >>
      `ricf_remaining_selected_use p s` by
        (fs[ricf_certificate_live_def, EVERY_MEM] >>
         qpat_x_assum `!entry. MEM entry certificates ==> _`
           (qspec_then `(p,[])` mp_tac) >> simp[ricf_visit_owner_state_def]) >>
      qexistsl_tac [`stk`,`tn`] >> irule ricf_certificate_owner_suspend >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `ricf_certificate_readonly _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ricf_certificate_readonly_def]) >>
  disch_then (qspecl_then [`p`,`frames0`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [
    `<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: inner`,
    `anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_call >> metis_tac[]
QED

Theorem ricf_history_certificates_call:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  wf_function fn /\ ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occ_frame_reachable vs C stk PG G tn fn callinst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\ occurrence_syntax_origin fn a H /\
  ricf_history_certificates vs C log_of stk PG G tn fn callinst s a U B
    history certificates /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_history_certificates vs C log_of
    (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    n (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (ricf_phase_push <|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> history)
    (ricf_phase_push <|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> certificates)
Proof
  strip_tac >> rw[ricf_history_certificates_def]
  >- (irule ricf_chosen_ledger_call >>
      fs[ricf_history_certificates_def] >> metis_tac[])
  >- (irule ricf_certificate_coverage_push >>
      qexists_tac `s` >> fs[ricf_history_certificates_def])
  >- (irule ricf_certificate_live_push >>
      qexists_tac `s` >> fs[ricf_history_certificates_def]) >>
  irule ricf_certificate_readonly_call >> metis_tac[]
QED

Theorem ricf_certificate_live_inherited[local]:
  ricf_certificate_live s certificates ==>
  ricf_certificate_live t (FILTER (\entry. SND entry <> []) certificates)
Proof
  simp[ricf_certificate_live_def, EVERY_MEM, MEM_FILTER] >>
  rpt strip_tac >> Cases_on `entry` >> gvs[] >>
  rename1 `MEM (p,pre) certificates` >>
  qpat_x_assum `!entry. MEM entry certificates ==> _`
    (qspec_then `(p,pre)` mp_tac) >> simp[ricf_visit_owner_state_def]
QED

Theorem ricf_history_certificates_block:
  ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B
    history certificates /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_history_certificates vs C log_of stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 a U B
    (FILTER (\entry. SND entry <> []) history)
    (FILTER (\entry. SND entry <> []) certificates)
Proof
  simp[ricf_history_certificates_def] >> strip_tac >> rpt conj_tac
  >- (irule ricf_chosen_ledger_block >> metis_tac[])
  >- (irule ricf_certificate_coverage_inherited >> qexists_tac `s` >> simp[])
  >- (irule ricf_certificate_live_inherited >> qexists_tac `s` >> simp[]) >>
  irule ricf_certificate_readonly_block >> metis_tac[]
QED

Theorem ricf_certificate_readonly_subset[local]:
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
  set next SUBSET set certificates ==>
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B next
Proof
  simp[ricf_certificate_readonly_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ricf_certificate_readonly_return[local]:
  ricf_certificate_readonly vs C log_of (f::stk) PG G tn fn rinst s
    (u::U) B certificates /\
  occ_frame_reachable vs C (f::stk) PG G tn fn rinst s n a (u::U) B HP H /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_certificate_readonly vs C log_of stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) U
    (DRESTRICT B {id | FST id <> a}) (ricf_phase_pop certificates)
Proof
  strip_tac >> drule occ_frame_reachable_owner_fresh >> strip_tac >>
  rw[ricf_certificate_readonly_def, ricf_phase_pop_def, MEM_MAP, MEM_FILTER] >>
  rename1 `MEM entry certificates` >> Cases_on `entry` >> gvs[] >>
  rename1 `MEM (p,frames0) certificates` >>
  qpat_x_assum `ricf_certificate_readonly _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ricf_certificate_readonly_def]) >>
  disch_then (qspecl_then [`p`,`frames0`] mp_tac) >> simp[] >> strip_tac >>
  `p.rpe_owner <> a` by
    (`ALL_DISTINCT (a::MAP (\u. u.of_owner) (u::U))` by simp[] >>
     metis_tac[ricf_aligned_origin_owner_old]) >>
  Cases_on `inner` >> gvs[] >>
  rename1 `ricf_aligned_origin_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (head::rest) _ _ _` >>
  `head = f /\ rest ++ anchor::tail = stk` by fs[ricf_aligned_origin_at_def] >>
  gvs[] >> qexistsl_tac [`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_restrict_owner >> simp[] >>
  drule_all ricf_aligned_origin_nested_return >>
  simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem ricf_certificate_live_pop[local]:
  ricf_certificate_live s certificates ==>
  ricf_certificate_live t (ricf_live_ledger t (ricf_phase_pop certificates))
Proof
  simp[ricf_certificate_live_def, EVERY_MEM] >> rpt strip_tac >>
  Cases_on `entry` >> gvs[ricf_live_ledger_member] >>
  rename1 `ricf_active_use p frames t` >>
  Cases_on `frames = []` >- fs[ricf_active_use_owner, ricf_visit_owner_state_def] >>
  fs[ricf_phase_pop_def, MEM_MAP, MEM_FILTER] >>
  rename1 `MEM old_entry certificates` >> Cases_on `old_entry` >> gvs[] >>
  rename1 `MEM (p,frames0) certificates` >>
  `ricf_remaining_selected_use p (ricf_visit_owner_state frames0 s)` by
    (qpat_x_assum `!entry. MEM entry certificates ==> _`
       (qspec_then `(p,frames0)` mp_tac) >> simp[]) >>
  Cases_on `frames0` >> gvs[] >> rename1 `ricf_visit_owner_state (head::rest) s` >>
  Cases_on `rest` >> fs[ricf_visit_owner_state_def]
QED

Theorem ricf_history_certificates_return:
  ricf_history_certificates vs C log_of (f::stk) PG G tn fn rinst s a (u::U) B
    history certificates /\
  occ_frame_reachable vs C (f::stk) PG G tn fn rinst s n a (u::U) B HP H /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  s'.vs_current_bb = f.cf_state.vs_current_bb /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_history_certificates vs C log_of stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    u.of_owner U (DRESTRICT B {id | FST id <> a})
    (ricf_phase_pop history)
    (ricf_live_ledger (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (ricf_phase_pop certificates))
Proof
  simp[ricf_history_certificates_def] >> strip_tac >> rpt conj_tac
  >- (irule ricf_chosen_ledger_return >> metis_tac[])
  >- (irule ricf_certificate_coverage_pop >> conj_tac
      >- (qexists_tac `f` >> simp[] >>
          fs[ricf_chosen_ledger_def, EVERY_MEM] >> rpt strip_tac >>
          qpat_x_assum `!entry. MEM entry history ==> _`
            (qspec_then `(p,pre)` mp_tac) >>
          simp[ricf_phase_entry_def] >> strip_tac >> Cases_on `pre` >> gvs[]) >>
      qexists_tac `s` >> simp[])
  >- (irule ricf_certificate_live_pop >> qexists_tac `s` >> simp[]) >>
  irule ricf_certificate_readonly_subset >>
  qexists_tac `ricf_phase_pop certificates` >>
  simp[ricf_live_ledger_subset] >>
  irule ricf_certificate_readonly_return >> metis_tac[]
QED

Theorem ricf_chosen_support_activate:
  ricf_chosen_support vs C log_of a p.rpe_fn B E /\
  ricf_history_origin vs C
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn) p stk PG G tn /\
  p.rpe_owner = a /\ 0 < p.rpe_size /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) ==>
  ricf_chosen_support vs C log_of a p.rpe_fn B (p.rpe_dst INSERT E)
Proof
  rw[ricf_chosen_support_def] >> Cases_on `id = p.rpe_dst` >> gvs[]
  >- (qexistsl_tac [`p`,`stk`,`PG`,`G`,`tn`] >> simp[]) >> metis_tac[]
QED

Theorem ricf_chosen_ledger_activate[local]:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occ_frame_reachable vs C stk PG G tn p.rpe_fn
    (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before n a U B HP H /\
  ricf_chosen_ledger vs C log_of stk PG G tn p.rpe_fn p.rpe_before a U B history /\
  ricf_history_origin vs C
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn) p stk PG G tn /\
  p.rpe_owner = a /\ 0 < p.rpe_size /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
  active_inst p.rpe_fn (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before /\
  (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode = MCOPY /\
  step_inst fuel C (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before = OK p.rpe_after ==>
  ricf_chosen_ledger vs C log_of stk PG
    (step_prov PG G (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
      p.rpe_before p.rpe_after tn) p.rpe_fn
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
    a U B ((p,[])::history)
Proof
  strip_tac >>
  `~is_terminator (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode /\
   (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `ricf_chosen_ledger vs C log_of stk PG
    (step_prov PG G (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
      p.rpe_before p.rpe_after tn) p.rpe_fn
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
    a U B history` by
    (drule_all ricf_chosen_ledger_next >> simp[occurrence_sites_step_def]) >>
  fs[ricf_chosen_ledger_def] >> simp[ricf_phase_entry_def] >>
  irule ricf_history_cursor_activate >> qexists_tac `stk` >> simp[]
QED

Theorem ricf_event_selected_not_before[local]:
  ricf_event_ok e bb ==>
  ?j. ricf_selected_position e bb j /\ e.rfe_index <= j
Proof
  strip_tac >>
  `e.rfe_sites <> []` by
    (strip_tac >> fs[ricf_event_ok_def, ricf_try_forward_def, AllCaseEqs()] >> gvs[]) >>
  `?ri pos rest. e.rfe_sites = (ri,pos)::rest` by
    (Cases_on `e.rfe_sites` >> fs[] >>
     rename1 `e.rfe_sites = head::tail` >> Cases_on `head` >> simp[]) >>
  `?j. findi (\el. el.inst_id = ri.inst_id) bb.bb_instructions = SOME j /\
       e.rfe_index <= j` by
    (qpat_x_assum `ricf_event_ok _ _` mp_tac >>
     simp[ricf_event_ok_def, ricf_try_forward_def] >>
     strip_tac >> gvs[AllCaseEqs()] >>
     Cases_on `findi (\el. el.inst_id = ri.inst_id) bb.bb_instructions` >>
     gvs[]) >>
  qexists_tac `j` >> simp[ricf_selected_position_def] >> metis_tac[MEM]
QED

Theorem ricf_located_event_remaining_after_copy[local]:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  s.vs_current_bb = (EL b fn.fn_blocks).bb_label /\ s.vs_inst_idx = e.rfe_index ==>
  ?j. ricf_selected_position e (EL b fn.fn_blocks) j /\ SUC s.vs_inst_idx <= j
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule ricf_event_selected_not_before >> strip_tac >>
  `MAP (\i. i.inst_id) (EL b fn.fn_blocks).bb_instructions =
   MAP (\i. i.inst_id) current.bb_instructions` by
    (fs[ricf_block_edit_def, LIST_REL_EL_EQN, LIST_EQ_REWRITE] >>
     rpt strip_tac >> first_x_assum (qspec_then `x` mp_tac) >>
     simp[ricf_inst_edit_def, EL_MAP]) >>
  `ricf_selected_position e (EL b fn.fn_blocks) j` by
    (fs[ricf_selected_position_def] >>
     drule findi_inst_ids >> disch_then (qspec_then `inst.inst_id` assume_tac) >>
     metis_tac[]) >>
  `j <> e.rfe_index` by
    (strip_tac >> gvs[] >>
     drule_all ricf_chosen_selected_opcode >> strip_tac >>
     drule ricf_event_copy_shape >> strip_tac >>
     fs[ricf_event_copy_def] >>
     drule ricf_block_edit_EL >> strip_tac >>
     qpat_x_assum `!i. _ ==> ricf_inst_edit _ _`
       (qspec_then `e.rfe_index` mp_tac) >> simp[ricf_inst_edit_def]) >>
  qexists_tac `j` >> simp[]
QED

Theorem ricf_history_origin_remaining_start[local]:
  ricf_history_origin vs C ctx0 log p stk PG G tn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts p.rpe_fn)) ==>
  ricf_remaining_selected_use p
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
Proof
  simp[ricf_history_origin_def] >> rpt strip_tac >>
  `p.rpe_before.vs_current_bb = p.rpe_block.bb_label /\
   p.rpe_before.vs_inst_idx = p.rpe_event.rfe_index` by
    fs[ricf_source_copy_payload_def] >>
  `p.rpe_before.vs_current_bb = (EL b p.rpe_fn.fn_blocks).bb_label` by metis_tac[] >>
  drule_all ricf_located_event_remaining_after_copy >> strip_tac >>
  `(ricf_event_copy p.rpe_event p.rpe_block).inst_opcode = MCOPY` by
    (drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >> metis_tac[]) >>
  `~is_terminator (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode` by
    simp[is_terminator_def] >>
  `p.rpe_after.vs_current_bb = p.rpe_before.vs_current_bb` by
    (qpat_x_assum `ricf_source_copy_payload _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ricf_source_copy_payload_def]) >>
     drule_all step_preserves_control_flow >> metis_tac[]) >>
  simp[ricf_remaining_selected_use_def] >> metis_tac[]
QED

Theorem ricf_history_certificates_activate:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occ_frame_reachable vs C stk PG G tn p.rpe_fn
    (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before n a U B HP H /\
  ricf_history_certificates vs C log_of stk PG G tn p.rpe_fn
    (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before a U B
    history certificates /\
  ricf_history_origin vs C
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn) p stk PG G tn /\
  p.rpe_owner = a /\ 0 < p.rpe_size /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
  wf_function p.rpe_fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts p.rpe_fn)) /\
  active_inst p.rpe_fn (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before /\
  (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode = MCOPY /\
  step_inst fuel C (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before = OK p.rpe_after /\
  active_inst p.rpe_fn next
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx) ==>
  ricf_history_certificates vs C log_of stk PG
    (step_prov PG G (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
      p.rpe_before p.rpe_after tn) p.rpe_fn next
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
    a U B ((p,[])::history) ((p,[])::certificates)
Proof
  strip_tac >>
  `~is_terminator (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode /\
   (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `ricf_history_certificates vs C log_of stk PG
    (step_prov PG G (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
      p.rpe_before p.rpe_after tn) p.rpe_fn next
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
    a U B history certificates` by
    (drule_all ricf_history_certificates_next >> simp[occurrence_sites_step_def]) >>
  `ricf_remaining_selected_use p
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)` by
    metis_tac[ricf_history_origin_remaining_start] >>
  simp[ricf_history_certificates_def] >> rpt conj_tac
  >- (irule ricf_chosen_ledger_activate >>
      fs[ricf_history_certificates_def] >> metis_tac[])
  >- (fs[ricf_history_certificates_def, ricf_certificate_coverage_def,
        SUBSET_DEF, MEM] >> metis_tac[])
  >- fs[ricf_history_certificates_def, ricf_certificate_live_def,
       ricf_visit_owner_state_def] >>
  fs[ricf_history_certificates_def, ricf_certificate_readonly_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
