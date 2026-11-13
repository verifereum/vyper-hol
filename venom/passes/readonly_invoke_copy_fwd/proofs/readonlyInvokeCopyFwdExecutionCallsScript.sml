Theory readonlyInvokeCopyFwdExecutionCalls
Ancestors
  readonlyInvokeCopyFwdExecutionCallInstall readonlyInvokeCopyFwdExecutionShape
  readonlyInvokeCopyFwdExecutionEntry readonlyInvokeCopyFwdExecutionRunner
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecutionCoverage
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHeterogeneousMapOrigins
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdOpaque
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs occurrenceGeometry occurrenceOrigin
  o1LowerDloadOccurrence o1LowerDloadPtrDiscipline o1LowerDloadGhost
  o1PassContract ptrDiscipline contextCodegenRel reachableFnSim
  venomExecSemantics venomExecProofs venomFnInstsProofs venomWf venomState venomInst
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
