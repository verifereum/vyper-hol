Theory readonlyInvokeCopyFwdExecutionRunner
Ancestors
  readonlyInvokeCopyFwdExecutionReturnBridge readonlyInvokeCopyFwdExecutionBoundary
  readonlyInvokeCopyFwdExecutionReturn
  readonlyInvokeCopyFwdExecutionEntry readonlyInvokeCopyFwdHeterogeneousLifecycle
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdExecutionHistory
  readonlyInvokeCopyFwdLiveCertificates
  readonlyInvokeCopyFwdExecutionCoverage
  readonlyInvokeCopyFwdExecutionInvokeTerminal
  o1LowerDloadOccurrence o1LowerDloadPtrDiscipline o1LowerDloadGhost
  reachableFnSim passSimulationDefs passSharedProps opcodeClass ptrDiscipline o1PassContract unitShapeDefs
  ctxLookupAgreeHelpers allocaFrontierBound
  stateEquiv stateEquivProps stateFrame
  venomExecSemantics venomInstProofs1 venomWf venomState venomInst
  finite_map list pred_set

Theorem ricf_execution_recursive_return:
  fn_sim_below D vs C Ct
    (ricf_execution_boundary vs C mid_of log_of D a (u::U) B0 E0 outer_history outer_certificates current
      (sites::maps) (caller::targets))
    (ricf_execution_return vs C Ct mid_of log_of D a (u::U) B0 E0 outer_history outer_certificates current
      (sites::maps) (caller::targets)) (SUC k) /\
  MEM fn C.ctx_functions /\ lookup_function fn.fn_name Ct.ctx_functions = SOME fn' /\
  ricf_execution_boundary vs C mid_of log_of D a (u::U) B0 E0 outer_history outer_certificates current
    (sites::maps) (caller::targets) (f::stk) PG FEMPTY tn0 fn cs ct /\
  block_reach vs C (f::stk) PG FEMPTY tn0 fn cs /\
  run_blocks k C fn cs = IntRet ret se /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ?m te tn t' n history certificates.
    run_blocks m Ct fn' ct = IntRet ret te /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state caller te)) = SOME t' /\
    FILTER (\entry. SND entry <> []) history = outer_history /\
    FILTER (\entry. SND entry <> []) certificates = outer_certificates /\
    ricf_analyzed_origins vs C stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      u.of_owner U B0 (ricf_phase_pop history) sites maps /\
    ricf_history_certificates vs C log_of stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      u.of_owner U B0 (ricf_phase_pop history)
      (ricf_live_ledger (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
        (ricf_phase_pop certificates)) /\
    ricf_execution_invariant vs C D stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      n u.of_owner U B0 u.of_params
      (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs)))
      (ricf_live_ledger (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
        (ricf_phase_pop certificates)) E0 sites maps targets
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
Proof
  strip_tac >>
  `?m te Gr tn. run_blocks m Ct fn' ct = IntRet ret te /\
    ricf_execution_return vs C Ct mid_of log_of D a (u::U) B0 E0 outer_history outer_certificates current
      (sites::maps) (caller::targets) (f::stk) PG Gr tn fn ret se te` by
    (qpat_x_assum `fn_sim_below _ _ _ _ _ _ _`
       (mp_tac o SIMP_RULE std_ss [fn_sim_below_def]) >>
     disch_then (qspecl_then [`k`,`f::stk`,`PG`,`FEMPTY`,`tn0`,`fn`,`fn'`,`cs`,`ct`]
       mp_tac) >>
     impl_tac >- simp[terminates_def] >> strip_tac >>
     Cases_on `run_blocks m Ct fn' ct` >> gvs[fn_run_rel_def] >> metis_tac[]) >>
  drule_all ricf_execution_return_resume >> strip_tac >>
  qexistsl_tac [`m`,`te`,`tn`,`t'`,`n`,`history`,`certificates`] >> simp[]
QED

Theorem ricf_execution_unchanged_invoke_return:
  ricf_execution_invariant vs C D stk PG G tn caller i s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_analyzed_origins vs C stk PG G tn caller i s a U B history sites maps /\
  ricf_history_certificates vs C log_of stk PG G tn caller i s a U B
    history certificates /\
  ricf_copy_coverage
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) caller)
    caller (log_of caller) a history s /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ricf_full_alloca_copies caller /\ ricf_src_alloca caller /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  opaque_use_ok caller /\ active_inst caller i s /\
  i.inst_opcode = INVOKE /\ j.inst_opcode = INVOKE /\ j.inst_outputs = i.inst_outputs /\
  decode_invoke i = SOME (nm,ops) /\ decode_invoke j = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  lookup_function nm Ct.ctx_functions = SOME callee' /\
  fn_entry_label callee' = fn_entry_label callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ricf_mapped_support n B E (MAP (op_prov G) ops) FEMPTY sites /\
  o1_fn_shape C callee /\ ricf_function_edit callee (mid_of callee) /\
  f = <|cf_fn := caller; cf_inst := i; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
  u = <|of_owner := a; of_prov := H; of_params := HP|> /\
  fn_sim_below D vs C Ct
    (ricf_execution_boundary vs C mid_of log_of D n (u::U) B E
      (ricf_phase_push f history) (ricf_phase_push f certificates)
      sites (sites::maps) (t::targets))
    (ricf_execution_return vs C Ct mid_of log_of D n (u::U) B E
      (ricf_phase_push f history) (ricf_phase_push f certificates)
      sites (sites::maps) (t::targets)) (SUC k) /\
  run_blocks k C callee cs = IntRet ret se /\
  bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME s' /\
  active_inst caller next (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?m t' next_n ret_tn.
    step_inst m Ct j t = OK t' /\
    FILTER (\entry. SND entry <> [])
      (ricf_live_ledger (s' with vs_inst_idx := SUC s.vs_inst_idx) certificates) =
      FILTER (\entry. SND entry <> []) certificates /\
    ricf_copy_coverage
      (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) caller)
      caller (log_of caller) a history (s' with vs_inst_idx := SUC s.vs_inst_idx) /\
    ricf_mapped_support a B E PG (DRESTRICT G (COMPL (set i.inst_outputs))) sites /\
    ricf_analyzed_origins vs C stk PG
      (DRESTRICT G (COMPL (set i.inst_outputs)))
      (ret_tn with t_var := DRESTRICT tn.t_var (COMPL (set i.inst_outputs)))
      caller next (s' with vs_inst_idx := SUC s.vs_inst_idx)
      a U B history sites maps /\
    ricf_history_certificates vs C log_of stk PG
      (DRESTRICT G (COMPL (set i.inst_outputs)))
      (ret_tn with t_var := DRESTRICT tn.t_var (COMPL (set i.inst_outputs)))
      caller next (s' with vs_inst_idx := SUC s.vs_inst_idx) a U B history
      (ricf_live_ledger (s' with vs_inst_idx := SUC s.vs_inst_idx) certificates) /\
    ricf_execution_invariant vs C D stk PG
      (DRESTRICT G (COMPL (set i.inst_outputs)))
      (ret_tn with t_var := DRESTRICT tn.t_var (COMPL (set i.inst_outputs)))
      caller next (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC s.vs_inst_idx)
      next_n a U B HP (DRESTRICT H (COMPL (set i.inst_outputs)))
      (ricf_live_ledger (s' with vs_inst_idx := SUC s.vs_inst_idx) certificates) E
      sites maps targets
      (ret_tn with t_var := DRESTRICT tn.t_var (COMPL (set i.inst_outputs)))
Proof
  strip_tac >> drule_all ricf_execution_unchanged_call_entry >> strip_tac >>
  `frame_reachable vs C stk PG G tn caller i s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM caller C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `wf_function caller` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `s'.vs_current_bb =
    (adopt_return_fmp ret (merge_callee_state s se)).vs_current_bb` by
    (irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]) >>
  `s'.vs_current_bb = s.vs_current_bb` by
    (Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `ricf_copy_coverage
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) caller)
    caller (log_of caller) a history (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (mp_tac (Q.INST [`ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
         (readonly_mem_analyze C) caller`, `fn` |-> `caller`,
       `log` |-> `log_of (caller : ir_function)`,
       `ledger` |-> `history`, `s` |-> `s`, `inst` |-> `i`,
       `u` |-> `s' with vs_inst_idx := SUC s.vs_inst_idx`]
       (INST_TYPE [alpha |-> ``:call_frame``] ricf_copy_coverage_ordinary)) >> simp[]) >>
  `FILTER (\entry. SND entry <> [])
      (ricf_live_ledger (s' with vs_inst_idx := SUC s.vs_inst_idx) certificates) =
    FILTER (\entry. SND entry <> []) certificates` by
    (mp_tac (Q.INST [`s` |-> `s`,
       `t` |-> `s' with vs_inst_idx := SUC s.vs_inst_idx`,
       `certificates` |-> `certificates`] ricf_certificate_live_outer_retire) >>
     fs[ricf_history_certificates_def]) >>
  `block_reach vs C (f::stk) (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) callee cs` by
    (gvs[] >> irule frame_reachable_call_block_reach >> metis_tac[]) >>
  `setup_callee callee' args' t = SOME ct` by
    (qpat_x_assum `fn_entry_label callee' = _` mp_tac >>
     Cases_on `callee.fn_blocks` >> Cases_on `callee'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, setup_callee_def]) >>
  `MEM callee C.ctx_functions /\ callee.fn_name = nm /\ opaque_use_ok callee` by
    (fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     metis_tac[lookup_function_MEM, lookup_function_selected_name]) >>
  `bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
   active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    gvs[] >>
  mp_tac (Q.INST [`a` |-> `n`, `B0` |-> `B`, `E0` |-> `E`,
    `outer_history` |-> `ricf_phase_push f history`,
    `outer_certificates` |-> `ricf_phase_push f certificates`,
    `current` |-> `sites`, `caller` |-> `t`, `fn` |-> `callee`,
    `fn'` |-> `callee'`, `PG` |-> `MAP (op_prov G) ops`,
    `tn0` |-> `tn with t_var := FEMPTY`] ricf_execution_recursive_return) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `m` (qx_choose_then `te`
    (qx_choose_then `ret_tn` (qx_choose_then `t'` (qx_choose_then `next_n`
      (qx_choose_then `history1` (qx_choose_then `certificates1` strip_assume_tac))))))) >>
  `ricf_phase_pop history1 = history /\
   ricf_phase_pop certificates1 = certificates` by
    metis_tac[ricf_phase_pop_outer] >>
  qexistsl_tac [`m`,`t'`,`next_n`,`ret_tn`] >> simp[Once step_inst_def] >>
  gvs[] >> irule ricf_mapped_support_provenance_restrict >> first_assum ACCEPT_TAC
QED
