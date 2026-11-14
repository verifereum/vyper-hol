(* Actual positive erased-copy execution with an original-syntax mask. *)
Theory readonlyInvokeCopyFwdOperationalPositiveCopy
Ancestors
  readonlyInvokeCopyFwdLedgerActivation readonlyInvokeCopyFwdCopyAnnotations
  readonlyInvokeCopyFwdGlobalSupport readonlyInvokeCopyFwdSupportSeparation
  readonlyInvokeCopyFwdHistoryReadExceptions
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdStepsCore
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryVisitAccess
  readonlyInvokeCopyFwdHistoryAvailability readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdPlan
  o1LowerDloadOccurrence occurrenceGeometry venomInst mem2varProofs
  venomWfProps o1PassContract finite_map list pred_set words

Definition ricf_original_copy_ids_def:
  ricf_original_copy_ids C = {did | ?fn da dr dst sv sz ci.
    MEM fn C.ctx_functions /\ MEM da (fn_insts fn) /\
    da.inst_opcode = ALLOCA /\ da.inst_outputs = [dr] /\ did = da.inst_id /\
    MEM ci (fn_insts fn) /\ ci.inst_opcode = MCOPY /\
    ci.inst_operands = [Var dst;Var sv;sz] /\ ircf_alias fn dr dst}
End

Theorem ricf_operational_positive_copy:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  0 < w2n z /\ occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) /\
  ricf_cert_core D (ricf_original_copy_ids C) stk PG G tn fn
    sites maps targets G0 tn0 cur curs s t /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_support_agree B E tn0 s t /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  EVERY (\entry. ?ctxP logP.
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B entry) ledger /\
  cur = ricf_phase_ranges 0 ledger /\
  curs = ricf_phase_stack_ranges stk ledger /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\ wf_function fn /\
  access_ok lo G fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  ~in_revert_forward fn s /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] ==>
  ?did sid db sb un u.
    FLOOKUP H dst = SOME (a,did) /\ FLOOKUP H sv = SOME (a,sid) /\
    did IN ricf_original_copy_ids C /\ did <> sid /\
    FLOOKUP B (a,did) = SOME (db,w2n z) /\
    FLOOKUP B (a,sid) = SOME (sb,w2n z) /\
    un = tn0 with t_mem :=
      (tn0.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
      {db+q | q < w2n z /\ sb+q IN tn0.t_mem} /\
    u = mcopy db sb (w2n z) s /\
    step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
    step_inst fuel Ct nop t = OK t /\
    ricf_cert_core D (ricf_original_copy_ids C) stk PG G
      (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
      fn sites maps targets G0 un (cur UNION {(db,sb,w2n z)}) curs u t /\
    ricf_cert_core D (ricf_original_copy_ids C) stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn)
      fn sites maps targets G0 un (cur UNION {(db,sb,w2n z)}) curs
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    ricf_support_agree B (E UNION {(a,did)}) un u t /\
    ricf_global_support_origins vs C ctx0 a fn U stk B (E UNION {(a,did)})
Proof
  strip_tac >>
  drule_all ricf_located_event_operands_available >> strip_tac >> gvs[] >>
  `MEM fn C.ctx_functions` by metis_tac[occ_frame_reachable_annotation] >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks /\
   e.rfe_index < LENGTH (EL b fn.fn_blocks).bb_instructions /\
   (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY` by
    (drule_all ricf_located_event_source_block >> strip_tac >>
     drule_all ricf_located_event_source_descriptor >> strip_tac >>
     drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >> strip_tac >>
     fs[ricf_block_edit_def] >> metis_tac[EL_MEM, LIST_REL_LENGTH]) >>
  `MEM (ricf_event_copy e (EL b fn.fn_blocks)) (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM, ricf_event_copy_def]) >>
  `da.inst_id IN ricf_original_copy_ids C` by
    (simp[ricf_original_copy_ids_def] >> metis_tac[]) >>
  `da.inst_id <> sa.inst_id` by
    (strip_tac >>
     `da = sa` by
       (irule (Q.ISPEC `\i:instruction. i.inst_id` ALL_DISTINCT_MAP_IMP) >>
        simp[] >> qexists_tac `fn_insts fn` >> simp[]) >>
     `dr = sv` by gvs[] >>
     drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
     drule ricf_source_copy_not_destination >>
     fs[ricf_event_copy_def] >> metis_tac[]) >>
  drule_at (Pat `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ricf_located_copy_cert_activate_ledger >>
  simp[] >>
  disch_then (drule_at (Pat `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `ricf_located_event _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`nop`,`lo`,`E`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  `db < dimword (:256) /\ sb < dimword (:256)` by
    (`db+w2n z <= s.vs_alloca_next` by
       metis_tac[occurrence_geometry_site_bounds] >>
     `sb+w2n z <= s.vs_alloca_next` by
       metis_tac[occurrence_geometry_site_bounds] >> decide_tac) >>
  `(ricf_event_copy e (EL b fn.fn_blocks)).inst_outputs = []` by
    (`inst_wf (ricf_event_copy e (EL b fn.fn_blocks))` by
       (fs[venomWfTheory.fn_inst_wf_def, ricf_event_copy_def] >> metis_tac[EL_MEM]) >>
     gvs[venomWfTheory.inst_wf_def]) >>
  `G = ricf_effective_prov fn s G0 /\
   tn = ricf_effective_taint fn s tn0` by
    fs[ricf_cert_core_def, ricf_live_boundary_core_def,
       ricf_effective_prov_def, ricf_effective_taint_def] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[ricf_cert_core_def, ricf_live_boundary_core_def,
       ricf_frame_agree_def, taintAgreeTheory.taint_agree_def,
       venomStateTheory.venom_state_component_equality] >>
  `step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s =
     OK (mcopy db sb (w2n z) s)` by simp[] >>
  drule_all ricf_global_support_located_activate >> strip_tac >>
  `p.rpe_dst = (a,da.inst_id)` by
    (drule ricf_history_origin_original_allocas >> simp[] >> strip_tac >>
     gvs[] >>
     drule_all ricf_located_event_source_descriptor >> strip_tac >> gvs[] >>
     metis_tac[ssa_alloca_output_unique, MEM]) >>
  `ricf_global_support_origins vs C ctx0 a fn U stk B (E UNION {(a,da.inst_id)})`
    by metis_tac[] >>
  simp[] >>
  conj_tac >- simp[Once venomExecSemanticsTheory.step_inst_def] >>
  drule_at (Pat `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ricf_cert_copy_successor >>
  simp[arithmeticTheory.ADD_COMM] >>
  metis_tac[]
QED
