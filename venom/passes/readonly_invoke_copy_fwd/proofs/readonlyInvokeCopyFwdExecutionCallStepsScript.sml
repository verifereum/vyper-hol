Theory readonlyInvokeCopyFwdExecutionCallSteps
Ancestors
  readonlyInvokeCopyFwdExecutionCalls readonlyInvokeCopyFwdExecutionAssembly
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdHistory
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs
  o1LowerDloadOccurrence o1LowerDloadPtrDiscipline o1LowerDloadGhost
  passSharedProps passSimulationDefs ctxLookupAgreeHelpers
  ptrDiscipline ptrDisciplineControl reachableFnSim o1PassContract unitShapeDefs
  contextCodegenRel allocaFrontierBound
  venomExecSemantics venomExecProofs venomWf venomInst venomState
  finite_map list

Theorem ricf_execution_invoke_next:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ricf_full_alloca_copies C.ctx_functions /\ EVERY ricf_src_alloca C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  (!f. MEM f C.ctx_functions ==>
    ricf_logged_function_trace
      (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) f)
      f (log_of f) (mid_of f) /\ ricf_function_edit f (mid_of f) /\
    ?f'. lookup_function f.fn_name Ct.ctx_functions = SOME f' /\
      fn_entry_label f' = fn_entry_label f) /\
  (!a1 U1 B1 E1 history1 certificates1 sites1 maps1 targets1.
    fn_sim_below D vs C Ct
      (ricf_execution_boundary vs C mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1)
      (ricf_execution_return vs C Ct mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1) (SUC k)) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction tb t.vs_inst_idx = SOME j /\
  inst.inst_opcode = INVOKE /\ step_inst k C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?m v G1 tn1. step_inst m Ct j t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG G1 tn1 fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `active_inst fn inst s` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_point_def, ricf_execution_invariant_def,
       ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `wf_function fn /\ ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
   ricf_function_edit fn (mid_of fn) /\
   ricf_logged_function_trace
     (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
     fn (log_of fn) (mid_of fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[ricf_execution_point_control] >>
  `?cb. cb < LENGTH fn.fn_blocks /\
    s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
    inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions /\
    bb = EL cb fn.fn_blocks /\
    j = EL s.vs_inst_idx (EL cb (mid_of fn).fn_blocks).bb_instructions` by
    metis_tac[ricf_execution_instruction_position] >>
  `?nm ops callee args cs ret se.
    decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    run_blocks k C callee cs = IntRet ret se /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s se)) = SOME u` by
    (qpat_x_assum `step_inst k C inst s = OK u` mp_tac >>
     simp[Once step_inst_def] >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `MEM callee C.ctx_functions /\ callee.fn_name = nm` by
    metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
  `o1_fn_shape C callee /\ ricf_function_edit callee (mid_of callee)` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `?callee'. lookup_function nm Ct.ctx_functions = SOME callee' /\
    fn_entry_label callee' = fn_entry_label callee` by metis_tac[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks)` by
    metis_tac[] >>
  drule_all ricf_execution_point_invoke_return >> simp[]
QED
Theorem ricf_execution_invoke_terminal_result:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ricf_full_alloca_copies C.ctx_functions /\ EVERY ricf_src_alloca C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  (!f. MEM f C.ctx_functions ==>
    ricf_logged_function_trace
      (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) f)
      f (log_of f) (mid_of f) /\ ricf_function_edit f (mid_of f) /\
    ?f'. lookup_function f.fn_name Ct.ctx_functions = SOME f' /\
      fn_entry_label f' = fn_entry_label f) /\
  (!a1 U1 B1 E1 history1 certificates1 sites1 maps1 targets1.
    fn_sim_below D vs C Ct
      (ricf_execution_boundary vs C mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1)
      (ricf_execution_return vs C Ct mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1) (SUC k)) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction tb t.vs_inst_idx = SOME j /\
  inst.inst_opcode = INVOKE /\ terminates (step_inst k C inst s) /\
  (!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode) ==>
  ?m. block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn (step_inst k C inst s) (step_inst m Ct j t)
Proof
  strip_tac >>
  `active_inst fn inst s` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_point_def, ricf_execution_invariant_def,
       ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `wf_function fn /\ ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
   ricf_function_edit fn (mid_of fn) /\
   ricf_logged_function_trace
     (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
     fn (log_of fn) (mid_of fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[ricf_execution_point_control] >>
  `?cb. cb < LENGTH fn.fn_blocks /\
    s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
    inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions /\
    bb = EL cb fn.fn_blocks /\
    j = EL s.vs_inst_idx (EL cb (mid_of fn).fn_blocks).bb_instructions` by
    metis_tac[ricf_execution_instruction_position] >>
  `?nm ops callee args cs.
    decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    ((?se. run_blocks k C callee cs = Halt se) \/
     (?reason se. run_blocks k C callee cs = Abort reason se))` by
    (mp_tac (Q.INST [`i` |-> `inst`, `r` |-> `step_inst k C inst s`]
       ld_terminating_invoke_inversion) >>
     (impl_tac >- simp[]) >> strip_tac >>
     gvs[is_terminator_def] >> metis_tac[]) >>
  `MEM callee C.ctx_functions /\ callee.fn_name = nm` by
    metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
  `o1_fn_shape C callee /\ ricf_function_edit callee (mid_of callee)` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `?callee'. lookup_function nm Ct.ctx_functions = SOME callee' /\
    fn_entry_label callee' = fn_entry_label callee` by metis_tac[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks)` by
    metis_tac[] >>
  mp_tac (SPEC_ALL ricf_execution_point_invoke_terminal) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED
