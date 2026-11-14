(* Historical support has per-origin logs and current owner/function alignment. *)
Theory readonlyInvokeCopyFwdGlobalSupport
Ancestors
  readonlyInvokeCopyFwdSupportSeparation readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdHistoryAvailability readonlyInvokeCopyFwdHistoryReadExceptions
  readonlyInvokeCopyFwdOccurrenceAlias o1LowerDloadOccurrence occurrenceGeometry
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdProtectionOrigin
  readonlyInvokeCopyFwdHistoryVisitAccess readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdPlan
  internalReturnCopyFwdPlan invokeCopyFwdCommonDefs venomWfProps mem2varProofs
  readonlyInvokeCopyFwdOperationalSupport
  finite_map list pred_set pair alist

Definition ricf_live_owner_function_def:
  ricf_live_owner_function a fn U stk owner f <=>
    MEM (owner,f) ((a,fn)::ZIP (MAP (\u. u.of_owner) U,
                                      MAP (\cf. cf.cf_fn) stk))
End

Definition ricf_global_support_origins_def:
  ricf_global_support_origins vs C ctx0 a fn U stk B E <=>
    !id. id IN E ==> ?log p pstk PG G tn.
      ricf_history_origin vs C ctx0 log p pstk PG G tn /\
      p.rpe_dst = id /\ FLOOKUP B id = SOME (p.rpe_db,p.rpe_size) /\
      ricf_live_owner_function a fn U stk (FST id) p.rpe_fn
End

Theorem ricf_global_support_empty:
  ricf_global_support_origins vs C ctx0 a fn U stk B {}
Proof
  simp[ricf_global_support_origins_def]
QED

Theorem ricf_live_owner_function_unique:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  ricf_live_owner_function a fn U stk owner f /\
  ricf_live_owner_function a fn U stk owner g ==> f = g
Proof
  strip_tac >> drule occ_frame_reachable_stack_length >> strip_tac >>
  drule occ_frame_reachable_owner_fresh >> strip_tac >>
  `ALL_DISTINCT (MAP FST ((a,fn)::ZIP
      (MAP (\u. u.of_owner) U, MAP (\cf. cf.cf_fn) stk)))` by
    simp[MAP_ZIP] >>
  qpat_x_assum `ricf_live_owner_function a fn U stk owner f`
    (mp_tac o REWRITE_RULE [ricf_live_owner_function_def]) >>
  qpat_x_assum `ricf_live_owner_function a fn U stk owner g`
    (mp_tac o REWRITE_RULE [ricf_live_owner_function_def]) >>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11]
QED

Theorem ricf_live_owner_function_current:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  ricf_live_owner_function a fn U stk a f ==> f = fn
Proof
  strip_tac >>
  `ricf_live_owner_function a fn U stk a fn` by
    simp[ricf_live_owner_function_def] >>
  metis_tac[ricf_live_owner_function_unique]
QED

Theorem ricf_live_owner_function_push:
  ricf_live_owner_function a fn U stk owner f ==>
  ricf_live_owner_function n callee
    (<|of_owner := a; of_prov := H; of_params := HP |> :: U)
    (<|cf_fn := fn; cf_inst := inst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk) owner f
Proof
  simp[ricf_live_owner_function_def] >> metis_tac[]
QED

Theorem ricf_live_owner_function_pop:
  ricf_live_owner_function a fn (u::U) (f::stk) owner other /\ owner <> a ==>
  ricf_live_owner_function u.of_owner f.cf_fn U stk owner other
Proof
  simp[ricf_live_owner_function_def] >> metis_tac[]
QED

Theorem ricf_global_support_activate:
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_history_origin vs C ctx0 log p pstk PG G tn /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FST p.rpe_dst = a /\ p.rpe_fn = fn ==>
  ricf_global_support_origins vs C ctx0 a fn U stk B (E UNION {p.rpe_dst})
Proof
  rw[ricf_global_support_origins_def] >>
  metis_tac[ricf_live_owner_function_def, MEM]
QED

Theorem ricf_global_support_next:
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  occurrence_allocas_ok B a s /\ step_inst fuel C inst s = OK s' ==>
  ricf_global_support_origins vs C ctx0 a fn U stk
    (occurrence_sites_step a B inst s') E
Proof
  rw[ricf_global_support_origins_def] >> first_x_assum drule >> strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- metis_tac[occurrence_sites_step_preserves] >>
  fs[occurrence_sites_step_def] >> metis_tac[]
QED

Theorem ricf_global_support_call:
  ricf_global_support_origins vs C ctx0 a fn U stk B E ==>
  ricf_global_support_origins vs C ctx0 n callee
    (<|of_owner := a; of_prov := H; of_params := HP |> :: U)
    (<|cf_fn := fn; cf_inst := inst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk) B E
Proof
  rw[ricf_global_support_origins_def] >>
  metis_tac[ricf_live_owner_function_push]
QED

Theorem ricf_global_support_return:
  ricf_global_support_origins vs C ctx0 a fn (u::U) (f::stk) B E ==>
  ricf_global_support_origins vs C ctx0 u.of_owner f.cf_fn U stk
    (DRESTRICT B {id | FST id <> a}) {id | id IN E /\ FST id <> a}
Proof
  rw[ricf_global_support_origins_def, FLOOKUP_DRESTRICT] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[ricf_live_owner_function_pop]
QED

Theorem ricf_global_support_actual_next:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  occ_frame_reachable vs C stk PG (step_prov PG G inst s')
    (step_taint inst s s' tn) fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst s') HP (occurrence_step a HP H inst s') /\
  ricf_global_support_origins vs C ctx0 a fn U stk
    (occurrence_sites_step a B inst s') E
Proof
  strip_tac >> drule occ_frame_reachable_annotation >> strip_tac >>
  fs[occurrence_annotation_ok_def] >>
  metis_tac[occ_frame_reachable_next, ricf_global_support_next]
QED

Theorem ricf_global_support_actual_block:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s' /\ ~s'.vs_halted /\
  enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
  occ_frame_reachable vs C stk PG (entry_prov fn s' G)
    (entry_taint_vars fn s' tn) fn inst' s1 n a U B HP (entry_prov fn s' H) /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E
Proof
  metis_tac[occ_frame_reachable_block]
QED

Theorem ricf_global_support_located_activate:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK s' /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E ==>
  ?p. p.rpe_event = e /\ p.rpe_block = EL b fn.fn_blocks /\ p.rpe_fn = fn /\
    p.rpe_before = s /\ p.rpe_after = s' /\ p.rpe_owner = a /\
    ricf_history_origin vs C ctx0 log p stk PG G tn /\
    FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
    ricf_global_support_origins vs C ctx0 a fn U stk B (E UNION {p.rpe_dst})
Proof
  strip_tac >> drule_all ricf_located_event_actual_origin >> strip_tac >>
  drule occ_frame_reachable_annotation >> strip_tac >>
  `occurrence_allocas_ok B p.rpe_owner p.rpe_before` by
    fs[occurrence_annotation_ok_def] >>
  drule_all ricf_history_origin_endpoints >> strip_tac >>
  `FST p.rpe_dst = a` by
    (fs[ricf_history_origin_def, ricf_source_copy_payload_def] >> metis_tac[]) >>
  metis_tac[ricf_global_support_activate]
QED

(* Cross-log boundary: only the owner lookup, not a shared transformation log,
   identifies the original function of a historical destination. *)
Theorem ricf_global_source_support_separation:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_global_support_origins vs C ctxP a fn U stk B E /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
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
  `(a,ai.inst_id) NOTIN E` by
    (strip_tac >> fs[ricf_global_support_origins_def] >>
     first_x_assum drule >> strip_tac >>
     `p.rpe_fn = fn` by metis_tac[ricf_live_owner_function_current, FST] >>
     `ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
      ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
      ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn` by metis_tac[] >>
     drule_all ricf_history_origin_original_allocas >> strip_tac >>
     `ai = da` by
       (gvs[] >>
        irule (Q.ISPEC `\i:instruction. i.inst_id` ALL_DISTINCT_MAP_IMP) >>
        simp[] >> qexists_tac `fn_insts p.rpe_fn` >> simp[]) >>
     `icf_assign_root (dfg_build_function fn) {} dst' = sv` by gvs[] >>
     `ircf_alias fn sv dst'` by metis_tac[ircf_assign_root_alias] >>
     `MEM (EL b fn.fn_blocks) fn.fn_blocks /\
      e.rfe_index < LENGTH (EL b fn.fn_blocks).bb_instructions /\
      (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY` by
       (drule_all ricf_located_event_source_block >> strip_tac >>
        drule_all ricf_located_event_source_descriptor >> strip_tac >>
        drule ricf_located_event_validation >> strip_tac >>
        drule ricf_event_copy_shape >> strip_tac >>
        fs[ricf_block_edit_def] >> metis_tac[EL_MEM, LIST_REL_LENGTH]) >>
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
     goal_assum (drule_at Any) >> fs[ricf_event_copy_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> gvs[ricf_support_bytes_def] >>
  `0 < len /\ 0 < z` by decide_tac >>
  `(a,ai.inst_id) <> id` by (strip_tac >> gvs[]) >>
  drule_all occurrence_geometry_sites_disjoint >> decide_tac
QED

Theorem ricf_global_source_support_agree:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
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
  occurrence_natural_geometry lo a U B stk s /\ ricf_support_agree B E tn0 s t ==>
  !q. q < len /\ sb+q NOTIN tn0.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory
Proof
  strip_tac >> drule_all ricf_global_source_support_separation >> strip_tac >>
  `sb+len <= s.vs_alloca_next` by metis_tac[occurrence_geometry_site_bounds] >>
  metis_tac[ricf_support_separated_source_agree]
QED

Theorem ricf_global_located_copy_source_support_agree:
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
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
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
  strip_tac >> drule_all ricf_located_event_operands_available >> strip_tac >>
  drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
  drule_all ricf_global_source_support_separation >> strip_tac >>
  `sb+w2n z <= s.vs_alloca_next` by metis_tac[occurrence_geometry_site_bounds] >>
  metis_tac[ricf_support_separated_source_agree]
QED

Theorem ricf_global_support_actual_call:
  occ_frame_reachable vs C stk PG G tn fn callinst s n a U B HP H /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  occ_frame_reachable vs C
    (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (SUC n) n (<|of_owner := a; of_prov := H; of_params := HP|> :: U)
    B (MAP (op_prov H) ops) FEMPTY /\
  ricf_global_support_origins vs C ctx0 n callee
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U)
    (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk) B E
Proof
  metis_tac[occ_frame_reachable_call, ricf_global_support_call]
QED

Theorem ricf_global_support_actual_return:
  occ_frame_reachable vs C (f::stk) PG G tn fn ri s n a (u::U) B HP H /\
  ricf_global_support_origins vs C ctx0 a fn (u::U) (f::stk) B E /\
  active_inst fn ri s /\ step_inst fuel C ri s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  occ_frame_reachable vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    n u.of_owner U (DRESTRICT B {id | FST id <> a}) u.of_params
    (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs))) /\
  ricf_global_support_origins vs C ctx0 u.of_owner f.cf_fn U stk
    (DRESTRICT B {id | FST id <> a}) {id | id IN E /\ FST id <> a}
Proof
  metis_tac[occ_frame_reachable_ret, ricf_global_support_return]
QED
