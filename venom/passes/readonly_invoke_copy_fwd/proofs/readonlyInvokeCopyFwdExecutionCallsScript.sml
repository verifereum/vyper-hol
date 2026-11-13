Theory readonlyInvokeCopyFwdExecutionCalls
Ancestors
  readonlyInvokeCopyFwdExecutionCallInstall readonlyInvokeCopyFwdExecutionShape
  readonlyInvokeCopyFwdExecutionEntry readonlyInvokeCopyFwdExecutionRunner
  readonlyInvokeCopyFwdExecutionInvokeTerminal
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecutionCoverage
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdLiveCertificates readonlyInvokeCopyFwdHeterogeneousLifecycle
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHeterogeneousMapOrigins
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdOpaque
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs occurrenceGeometry occurrenceOrigin
  o1LowerDloadOccurrence o1LowerDloadPtrDiscipline o1LowerDloadGhost
  o1PassContract ptrDiscipline ptrDisciplineControl contextCodegenRel reachableFnSim
  stateFrame passSharedProps ctxLookupAgreeHelpers allocaFrontierBound
  venomExecSemantics venomExecProofs venomInstProofs1 venomFnInstsProofs venomWf venomState venomInst
  finite_map list pred_set

Theorem ricf_execution_actual_call_entry:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_analyzed_origins vs C stk PG G tn fn inst s a U B history sites maps /\
  ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B history certificates /\
  ricf_chosen_support vs C log_of a fn B E /\
  ricf_mapped_support a B E PG G sites /\
  ricf_copy_coverage
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) a history s /\
  ricf_logged_function_trace
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) (mid_of fn) /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  cb < LENGTH fn.fn_blocks /\
  s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks) /\
  j = EL s.vs_inst_idx (EL cb (mid_of fn).fn_blocks).bb_instructions /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  o1_fn_shape C callee /\ ricf_function_edit callee (mid_of callee) ==>
  ?callsites ops' args' ct.
    j.inst_opcode = INVOKE /\ j.inst_outputs = inst.inst_outputs /\
    decode_invoke j = SOME (nm,ops') /\ eval_operands ops' t = SOME args' /\
    setup_callee callee args' t = SOME ct /\
    ricf_execution_boundary vs C mid_of log_of D n
      (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B E
      (ricf_phase_push
        <|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> history)
      (ricf_phase_push
        <|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> certificates)
      callsites (sites::maps) (t::targets)
      (<|cf_fn := fn; cf_inst := inst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee cs ct
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
   wf_ssa fn /\ wf_function fn /\ ssa_form fn /\ fn_inst_wf fn /\
   opaque_use_ok fn /\ fn_inst_ids_distinct fn /\
   ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def,
        EVERY_MEM, wf_ssa_def, wf_function_def, fn_inst_ids_distinct_def,
        fn_insts_def, fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o,
        combinTheory.o_DEF] >> metis_tac[]) >>
  `occurrence_natural_geometry lo a U B stk s` by
    metis_tac[occ_frame_reachable_geometry, ptr_discipline_def] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    metis_tac[occ_frame_reachable_annotation] >>
  `occurrence_syntax_origin fn a H` by
    metis_tac[occ_frame_reachable_origin_certificate,
      occurrence_origin_certificate_current] >>
  qabbrev_tac `ps = MAP FST (FILTER (\entry.
    SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
    ricf_selected_position (FST entry).rpe_event
      (FST entry).rpe_block s.vs_inst_idx) history)` >>
  mp_tac (SPEC_ALL ricf_call_install |>
    Q.INST [`ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
       (readonly_mem_analyze C) fn`, `mid` |-> `mid_of fn`]) >>
  (impl_tac >- (fs[ricf_analyzed_origins_def] >> simp[Abbr `ps`])) >> strip_tac >>
  `j.inst_opcode = INVOKE /\ j.inst_outputs = inst.inst_outputs` by
    (qpat_assum `inst = EL _ _` (fn eq =>
     mp_tac (REWRITE_RULE [GSYM eq] (SPEC_ALL ricf_execution_logged_invoke_shape |>
      Q.INST [`ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
         (readonly_mem_analyze C) fn`, `log` |-> `log_of (fn:ir_function)`,
        `mid` |-> `mid_of fn`, `b` |-> `cb`, `i` |-> `s.vs_inst_idx`,
        `args` |-> `ops`]))) >> (impl_tac >- simp[]) >> strip_tac >> fs[]) >>
  `?ct. setup_callee callee args' t = SOME ct` by
    (Cases_on `callee.fn_blocks` >> gvs[setup_callee_def]) >>
  qexistsl_tac [`callsites`,`ops'`,`args'`,`ct`] >> simp[] >>
  mp_tac (SPEC_ALL ricf_execution_call_entry |>
    Q.INST [`caller` |-> `fn`, `callinst` |-> `inst`,
      `f` |-> `<|cf_fn := fn; cf_inst := inst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>`,
      `u` |-> `<|of_owner := a; of_prov := H; of_params := HP|>`]) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem ricf_execution_point_invoke_return:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  ricf_logged_function_trace
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) (mid_of fn) /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  cb < LENGTH fn.fn_blocks /\
  s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks) /\
  j = EL s.vs_inst_idx (EL cb (mid_of fn).fn_blocks).bb_instructions /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  lookup_function nm Ct.ctx_functions = SOME callee' /\
  fn_entry_label callee' = fn_entry_label callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  o1_fn_shape C callee /\ ricf_function_edit callee (mid_of callee) /\
  (!a1 U1 B1 E1 history1 certificates1 sites1 maps1 targets1.
    fn_sim_below D vs C Ct
      (ricf_execution_boundary vs C mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1)
      (ricf_execution_return vs C Ct mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1) (SUC k)) /\
  run_blocks k C callee cs = IntRet ret se /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?m v G1 tn1. step_inst m Ct j t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG G1 tn1 fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  drule_all ricf_execution_actual_call_entry >> strip_tac >>
  qabbrev_tac `saved = <|cf_fn := fn; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  qabbrev_tac `owner = <|of_owner := a; of_prov := H; of_params := HP|>` >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `wf_function fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (`u.vs_current_bb =
       (adopt_return_fmp ret (merge_callee_state s se)).vs_current_bb` by
       (irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]) >>
     Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `ricf_copy_coverage
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) a history (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (mp_tac (Q.INST [`ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
         (readonly_mem_analyze C) fn`, `fn` |-> `fn`,
       `log` |-> `log_of (fn:ir_function)`, `ledger` |-> `history`,
       `s` |-> `s`, `inst` |-> `inst`,
       `u` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`]
       (INST_TYPE [alpha |-> ``:call_frame``] ricf_copy_coverage_ordinary)) >> simp[]) >>
  `FILTER (\entry. SND entry <> [])
      (ricf_live_ledger (u with vs_inst_idx := SUC s.vs_inst_idx) certificates) =
    FILTER (\entry. SND entry <> []) certificates` by
    (mp_tac (Q.INST [`s` |-> `s`,
       `t` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`,
       `certificates` |-> `certificates`] ricf_certificate_live_outer_retire) >>
     fs[ricf_history_certificates_def]) >>
  `block_reach vs C (saved::stk) (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) callee cs` by
    (simp[Abbr `saved`] >> irule frame_reachable_call_block_reach >> metis_tac[]) >>
  `setup_callee callee' args' t = SOME ct` by
    (qpat_x_assum `fn_entry_label callee' = _` mp_tac >>
     Cases_on `callee.fn_blocks` >> Cases_on `callee'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, setup_callee_def]) >>
  `MEM callee C.ctx_functions /\ callee.fn_name = nm /\ opaque_use_ok callee` by
    (fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     metis_tac[lookup_function_MEM, lookup_function_selected_name]) >>
  `fn_sim_below D vs C Ct
    (ricf_execution_boundary vs C mid_of log_of D n (owner::U) B E
      (ricf_phase_push saved history) (ricf_phase_push saved certificates)
      callsites (sites::maps) (t::targets))
    (ricf_execution_return vs C Ct mid_of log_of D n (owner::U) B E
      (ricf_phase_push saved history) (ricf_phase_push saved certificates)
      callsites (sites::maps) (t::targets)) (SUC k)` by metis_tac[] >>
  mp_tac (Q.INST [`a` |-> `n`, `B0` |-> `B`, `E0` |-> `E`,
    `outer_history` |-> `ricf_phase_push saved history`,
    `outer_certificates` |-> `ricf_phase_push saved certificates`,
    `current` |-> `callsites`, `caller` |-> `t`, `fn` |-> `callee`,
    `fn'` |-> `callee'`, `PG` |-> `MAP (op_prov G) ops`,
    `tn0` |-> `tn with t_var := FEMPTY`, `f` |-> `saved`,
    `s'` |-> `u`]
    (Q.INST [`u` |-> `owner`] ricf_execution_recursive_return)) >>
  (impl_tac >- (simp[Abbr `saved`, Abbr `owner`] >> metis_tac[])) >>
  disch_then (qx_choose_then `m` (qx_choose_then `te`
    (qx_choose_then `ret_tn` (qx_choose_then `v` (qx_choose_then `next_n`
      (qx_choose_then `history2` (qx_choose_then `certificates2` strip_assume_tac))))))) >>
  `ricf_phase_pop history2 = history /\
   ricf_phase_pop certificates2 = certificates` by
    metis_tac[ricf_phase_pop_outer] >>
  `step_inst m Ct j t = OK v` by
    (gvs[Abbr `saved`, Abbr `owner`] >> simp[Once step_inst_def]) >>
  `ricf_mapped_support a B E PG (DRESTRICT G (COMPL (set inst.inst_outputs))) sites` by
    metis_tac[ricf_mapped_support_provenance_restrict] >>
  qexistsl_tac [`m`,`v`,`DRESTRICT G (COMPL (set inst.inst_outputs))`,
    `ret_tn with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))`] >>
  simp[] >> rewrite_tac[ricf_execution_point_def] >>
  qexistsl_tac [`next_n`,`B`,`HP`,`DRESTRICT H (COMPL (set inst.inst_outputs))`,
    `history`,`ricf_live_ledger (u with vs_inst_idx := SUC s.vs_inst_idx) certificates`,`E`] >>
  gvs[Abbr `saved`, Abbr `owner`]
QED

Theorem ricf_execution_point_invoke_terminal:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  ricf_logged_function_trace
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) (mid_of fn) /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  cb < LENGTH fn.fn_blocks /\
  s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks) /\
  j = EL s.vs_inst_idx (EL cb (mid_of fn).fn_blocks).bb_instructions /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  lookup_function nm Ct.ctx_functions = SOME callee' /\
  fn_entry_label callee' = fn_entry_label callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  o1_fn_shape C callee /\ ricf_function_edit callee (mid_of callee) /\
  (!a1 U1 B1 E1 history1 certificates1 sites1 maps1 targets1.
    fn_sim_below D vs C Ct
      (ricf_execution_boundary vs C mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1)
      (ricf_execution_return vs C Ct mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1) (SUC k)) /\
  ((?se. run_blocks k C callee cs = Halt se) \/
   (?reason se. run_blocks k C callee cs = Abort reason se)) ==>
  ?m. block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn (step_inst k C inst s) (step_inst m Ct j t)
Proof
  strip_tac >>
  qpat_x_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  drule_all ricf_execution_actual_call_entry >> strip_tac >>
  qabbrev_tac `saved = <|cf_fn := fn; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  qabbrev_tac `owner = <|of_owner := a; of_prov := H; of_params := HP|>` >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `block_reach vs C (saved::stk) (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) callee cs` by
    (simp[Abbr `saved`] >> irule frame_reachable_call_block_reach >> metis_tac[]) >>
  `setup_callee callee' args' t = SOME ct` by
    (qpat_x_assum `fn_entry_label callee' = _` mp_tac >>
     Cases_on `callee.fn_blocks` >> Cases_on `callee'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, setup_callee_def]) >>
  `MEM callee C.ctx_functions /\ callee.fn_name = nm` by
    metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
  mp_tac (SPEC_ALL ricf_execution_invoke_terminal |>
    Q.INST [
      `R` |-> `ricf_execution_boundary vs C mid_of log_of D n (owner::U) B E
        (ricf_phase_push saved history) (ricf_phase_push saved certificates)
        callsites (sites::maps) (t::targets)`,
      `Rret` |-> `ricf_execution_return vs C Ct mid_of log_of D n (owner::U) B E
        (ricf_phase_push saved history) (ricf_phase_push saved certificates)
        callsites (sites::maps) (t::targets)`,
      `P` |-> `ricf_execution_boundary vs C mid_of log_of D a U B0 E0
        outer_history outer_certificates sites maps targets`,
      `Pret` |-> `ricf_execution_return vs C Ct mid_of log_of D a U B0 E0
        outer_history outer_certificates sites maps targets`,
      `cstk` |-> `saved::stk`, `cPG` |-> `MAP (op_prov G) ops`,
      `cG` |-> `FEMPTY`, `ctn` |-> `tn with t_var := FEMPTY`,
      `i` |-> `inst`]) >>
  (impl_tac >- (simp[Abbr `saved`, Abbr `owner`] >> metis_tac[])) >> simp[]
QED
