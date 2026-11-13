(* Historical disagreement support is independent of current phase relevance. *)
Theory readonlyInvokeCopyFwdSupportSeparation
Ancestors
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryVisitAccess
  readonlyInvokeCopyFwdHistoryAvailability readonlyInvokeCopyFwdProtectionSelected
  readonlyInvokeCopyFwdHistoryReadExceptions
  internalReturnCopyFwdPlan occurrenceGeometry invokeCopyFwdCommonDefs
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdProtectionOrigin
  readonlyInvokeCopyFwdPlan
  venomWfProps mem2varProofs list finite_map pred_set

Theorem ricf_logged_trace_nonempty_original:
  ricf_logged_function_trace ctx0 fn log last /\ log <> [] ==>
  fn = FST (HD log)
Proof
  simp[Once ricf_logged_function_trace_cases] >> rpt strip_tac >> gvs[]
QED

Theorem ricf_located_events_same_original:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_located_event ctx0 other log round' b' es' prefix' e' current' ==>
  fn = other
Proof
  simp[ricf_located_event_def] >> rpt strip_tac >>
  `log <> []` by (strip_tac >> gvs[]) >>
  metis_tac[ricf_logged_trace_nonempty_original]
QED

Theorem ricf_isolated_assign_alias:
  !fn root v. ircf_alias fn root v ==>
  (!inst. MEM inst (fn_insts fn) /\ MEM (Var root) inst.inst_operands ==>
    ~is_pointer_preserving_op inst.inst_opcode) ==> v = root
Proof
  ho_match_mp_tac ircf_alias_ind >> rpt strip_tac >> gvs[] >>
  metis_tac[pointerConfinedDefsTheory.is_pointer_preserving_op_def]
QED

Theorem ricf_source_copy_not_destination:
  ricf_src_alloca fn /\ MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = MCOPY /\
  (EL k bb.bb_instructions).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\ MEM old (fn_insts fn) /\ old.inst_opcode = MCOPY /\
  old.inst_operands = [Var d;src;szop] /\ ircf_alias fn sv d ==> F
Proof
  strip_tac >>
  `!inst. MEM inst (fn_insts fn) /\ MEM (Var sv) inst.inst_operands ==>
     ~is_pointer_preserving_op inst.inst_opcode` by
    metis_tac[ricf_source_copy_isolated] >>
  `d = sv` by metis_tac[ricf_isolated_assign_alias] >> gvs[] >>
  fs[ricf_src_alloca_def] >>
  first_x_assum (qspecl_then [`bb`,`k`] mp_tac) >> simp[] >>
  metis_tac[listTheory.MEM, listTheory.HD]
QED

Theorem ricf_located_source_history_destination_distinct:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_history_origin vs C ctx0 log p stk PG G tn /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\ icf_is_alloca di /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] ==>
  (a,ai.inst_id) <> p.rpe_dst
Proof
  strip_tac >>
  `p.rpe_fn = fn` by
    (fs[ricf_history_origin_def] >> metis_tac[ricf_located_events_same_original]) >>
  `ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
   ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
   ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn` by metis_tac[] >>
  drule_all ricf_history_origin_original_allocas >> strip_tac >>
  strip_tac >>
  `ai = da` by
    (gvs[] >>
     irule (Q.ISPEC `\i:instruction. i.inst_id` ALL_DISTINCT_MAP_IMP) >>
     simp[] >> qexists_tac `fn_insts p.rpe_fn` >> simp[]) >>
  `icf_assign_root (dfg_build_function fn) {} dst' = sv` by gvs[] >>
  `ircf_alias fn sv dst'` by metis_tac[ircf_assign_root_alias] >>
  qpat_assum `ricf_located_event ctx0 fn log round b es prefix e current` mp_tac >>
  strip_tac >> drule_all ricf_located_event_source_block >> strip_tac >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks` by simp[EL_MEM] >>
  `e.rfe_index < LENGTH (EL b fn.fn_blocks).bb_instructions /\
   (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY` by
    (drule_all ricf_located_event_source_descriptor >> strip_tac >>
     drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >> strip_tac >>
     fs[ricf_event_copy_def, ricf_block_edit_def] >> metis_tac[LIST_REL_LENGTH]) >>
  `MEM (ricf_event_copy p.rpe_event p.rpe_block) (fn_insts fn) /\
   (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode = MCOPY` by
    (fs[ricf_history_origin_def] >>
     drule_all ricf_located_event_source_block >> strip_tac >>
     drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >> strip_tac >>
     fs[ricf_event_copy_def, ricf_block_edit_def] >>
     `p.rpe_event.rfe_index < LENGTH (EL b' fn.fn_blocks).bb_instructions` by
       metis_tac[LIST_REL_LENGTH] >>
     reverse conj_tac >- metis_tac[] >>
     simp[venomInstTheory.fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     qexists_tac `EL b' fn.fn_blocks` >> simp[EL_MEM]) >>
  irule ricf_source_copy_not_destination >>
  goal_assum (drule_at Any) >> fs[ricf_event_copy_def] >> metis_tac[]
QED

Theorem ricf_located_source_support_separation:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_support_origins vs C ctx0 log B E /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\ icf_is_alloca di /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  FLOOKUP B (a,ai.inst_id) = SOME (sb,len) /\
  occurrence_natural_geometry lo a U B stk s ==>
  (a,ai.inst_id) NOTIN E /\
  !q. q < len ==> sb+q NOTIN ricf_support_bytes B E
Proof
  strip_tac >>
  `!id. id IN E ==> (a,ai.inst_id) <> id` by
    (rpt strip_tac >> fs[ricf_support_origins_def] >>
     first_x_assum drule >> strip_tac >>
     metis_tac[ricf_located_source_history_destination_distinct]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[ricf_support_bytes_def] >>
  `0 < len /\ 0 < z` by decide_tac >>
  ` (a,ai.inst_id) <> id` by (strip_tac >> gvs[]) >>
  drule_all occurrence_geometry_sites_disjoint >> decide_tac
QED

Theorem ricf_support_separated_source_agree:
  ricf_support_agree B E tn s t /\ sb+len <= s.vs_alloca_next /\
  (!q. q < len ==> sb+q NOTIN ricf_support_bytes B E) ==>
  !q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory
Proof
  rw[ricf_support_agree_def] >> first_x_assum irule >> simp[]
QED

(* Actual source execution supplies the source key: no support exclusion or
   current-phase relevance is assumed here, even for historical support. *)
Theorem ricf_located_copy_source_support_agree:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  ricf_support_origins vs C ctx0 log B E /\
  occurrence_natural_geometry lo a U B stk s /\
  ricf_support_agree B E tn0 s t ==>
  ?dst sv z sa db sb.
    (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands =
      [Var dst;Var sv;Lit z] /\
    eval_operands (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands s =
      SOME [n2w db;n2w sb;z] /\
    MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
    sa.inst_outputs = [sv] /\ sa.inst_operands = [Lit z] /\
    FLOOKUP B (a,sa.inst_id) = SOME (sb,w2n z) /\
    (a,sa.inst_id) NOTIN E /\
    (!q. q < w2n z ==> sb+q NOTIN ricf_support_bytes B E) /\
    (!q. q < w2n z /\ sb+q NOTIN tn0.t_mem ==>
      read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory)
Proof
  strip_tac >>
  drule_all ricf_located_event_operands_available >> strip_tac >>
  drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
  drule_all ricf_located_source_support_separation >> strip_tac >>
  `sb + w2n z <= s.vs_alloca_next` by
    metis_tac[occurrence_geometry_site_bounds] >>
  metis_tac[ricf_support_separated_source_agree]
QED
