(* The source parameter phase before its compiled entry packet executes. *)
Theory fnFramePrefixEntry
Ancestors
  fnFramePrefix fnEntryParams fnEntryPlan fnEntryStep fnFrameBoundaryEntryParams
  codegenEntrySim codegenEntryRel fnBlockBodyHelpers fnBlockBodySteps
  contextCodegenRel frameRel unitShapeDefs stackPlanGen stackPlanTypes
  planExec stackOpSim asmSem venomExecSemantics venomInst venomState
  fcgDefs livenessDefs dfgDefs cfgDefs fnPlanLineage list rich_list arithmetic

Definition entry_frame_plan_def:
  entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 <=>
    generate_context_plan unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
    (!l. FLOOKUP entry.vs_labels l =
      OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cpl fn entry ast ra rest /\ mem0 = ast.as_memory /\
    (fn_has_retpc fn ==> FLOOKUP (build_offset_to_pc prog) (w2n ra) = SOME pc_ret) /\
    (?i r. i < LENGTH unit.cu_context.ctx_functions /\
      EL i unit.cu_context.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
      MEM fn.fn_name (fcg_analyze unit.cu_context).fcg_reachable /\
      asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp r.sr_plan)) /\
    (?k. k <= LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      s = entry_bind_pairs
        (entry_param_pairs entry (TAKE k (get_params (HD fn.fn_blocks).bb_instructions)))
        entry with vs_inst_idx := k)
End

Theorem entry_frame_plan_start:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  (!l. FLOOKUP entry.vs_labels l =
    OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
  fn_entry_state_rel cpl fn entry ast ra rest /\
  (fn_has_retpc fn ==> FLOOKUP (build_offset_to_pc prog) (w2n ra) = SOME pc_ret) /\
  i < LENGTH unit.cu_context.ctx_functions /\
  EL i unit.cu_context.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
  MEM fn.fn_name (fcg_analyze unit.cu_context).fcg_reachable /\
  asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp r.sr_plan) ==>
  entry_frame_plan rpolicy unit cpl prog fn entry
    (entry with vs_inst_idx := 0) ast ra pc_ret rest ast.as_memory
Proof
  rw[entry_frame_plan_def] >- metis_tac[] >>
  qexists_tac `0` >> simp[entry_prefix_zero]
QED

Theorem entry_frame_active_param:
  entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  active_inst fn inst s /\
  s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  inst = EL s.vs_inst_idx (get_params (HD fn.fn_blocks).bb_instructions) /\
  is_param_opcode inst.inst_opcode
Proof
  strip_tac >>
  qpat_x_assum `entry_frame_plan _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_frame_plan_def]) >>
  `s.vs_inst_idx = k` by fs[] >>
  `codegen_ready_fn fn` by metis_tac[body_fn_shape] >>
  `wf_function fn /\ fn.fn_blocks <> []` by
    fs[codegen_ready_fn_def, venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def] >>
  `s.vs_current_bb = (HD fn.fn_blocks).bb_label` by
    fs[fn_entry_state_rel_def, entry_bind_pairs_normal] >>
  qpat_x_assum `active_inst fn inst s`
    (strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
  `bb = HD fn.fn_blocks` by
    metis_tac[venomExecProofsTheory.same_label_same_block, HEAD_MEM] >>
  qpat_x_assum `bb = _` SUBST_ALL_TAC >>
  drule fnEntryStepTheory.get_params_el >> strip_tac >>
  conj_tac
  >- (qspec_then `(HD fn.fn_blocks).bb_instructions`
        strip_assume_tac get_params_suffix >>
      qpat_x_assum `EL s.vs_inst_idx _ = inst`
        (fn th => ONCE_REWRITE_TAC [SYM th]) >>
      qpat_assum `(HD fn.fn_blocks).bb_instructions = _`
        (fn th => simp[SimpLHS, Once th, EL_APPEND_EQN]) >> fs[]) >>
  metis_tac[]
QED

Theorem entry_frame_plan_next:
  entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  ?post.
    step_inst fuel unit.cu_context
      (EL s.vs_inst_idx (get_params (HD fn.fn_blocks).bb_instructions)) s = OK post /\
    entry_frame_plan rpolicy unit cpl prog fn entry
      (post with vs_inst_idx := SUC s.vs_inst_idx) ast ra pc_ret rest mem0
Proof
  strip_tac >>
  qpat_x_assum `entry_frame_plan _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_frame_plan_def]) >>
  `s.vs_inst_idx = k` by fs[] >>
  `codegen_ready_fn fn` by metis_tac[body_fn_shape] >>
  drule_all bounded_entry_param_shape >> strip_tac >>
  drule_all entry_prefix_step >> strip_tac >>
  qexists_tac `entry_bind_pairs
    (entry_param_pairs entry
      (TAKE (SUC k) (get_params (HD fn.fn_blocks).bb_instructions))) entry
      with vs_inst_idx := k` >>
  conj_tac >- metis_tac[] >>
  PURE_REWRITE_TAC [entry_frame_plan_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`i`, `r`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `SUC k` >> fs[]
QED

Theorem entry_frame_plan_ready:
  entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  ?n ast1.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn s ast1 ra rest mem0
Proof
  strip_tac >>
  qpat_x_assum `entry_frame_plan _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_frame_plan_def]) >>
  `s.vs_inst_idx = k` by fs[] >>
  `s = entry_bind_pairs
    (entry_param_pairs entry (get_params (HD fn.fn_blocks).bb_instructions)) entry
      with vs_inst_idx := LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    fs[] >>
  `codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn` by
    metis_tac[body_fn_shape] >>
  drule_all region_fn_plan >> strip_tac >>
  drule_all entry_block_plan >> strip_tac >>
  `!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)` by
    metis_tac[entry_step_spill_bound] >>
  `asm_block_at prog ast.as_pc
     (execute_plan cpl.cp_initial_fmp
       (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
   asm_block_at prog ast.as_pc
     (execute_plan cpl.cp_initial_fmp
       (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))` by
    (qpat_x_assum `asm_block_at _ _ (execute_plan _ r.sr_plan)` mp_tac >>
     qpat_assum `r.sr_plan = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[execute_plan_append, asm_block_at_append] >>
     rpt strip_tac >> fs[]) >>
  `ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  qspecl_then [`unit.cu_context`, `cpl`, `SND (compute_label_offsets prog)`,
    `build_offset_to_pc prog`, `prog`, `liveness_analyze fn`, `fn`,
    `cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
      unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name`,
    `cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context)`,
    `r.sr_spill_base`, `lbl_ctr`,
    `init_cleanup_plan_state
      (cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
        unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name)
      (cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context))
      r.sr_spill_base lbl_ctr`, `param_ops`, `ps1`, `r`, `entry`, `ast`,
    `ra`, `rest`, `s`] mp_tac entry_prefix_asm_exact >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then (qx_choose_then `ast1` strip_assume_tac) >>
  mp_tac (Q.INST
    [`fn` |-> `fn`, `liveness` |-> `liveness_analyze fn`,
     `ch` |-> `cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
       unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name`,
     `growth` |-> `cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context)`,
     `spill_base` |-> `r.sr_spill_base`, `lbl_ctr` |-> `lbl_ctr`,
     `ps0` |-> `init_cleanup_plan_state
       (cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
         unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name)
       (cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context))
       r.sr_spill_base lbl_ctr`,
     `ops` |-> `param_ops`, `ps1` |-> `ps1`]
    (SPEC_ALL entry_plan_normalize)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  drule_at (Pat `codegen_context_obligations _ _ _`) codegen_invoke_targets_retpc >>
  disch_then (assume_tac o SIMP_RULE (srw_ss())
    [ASSUME ``unit_shape_ok unit``]) >>
  `!l. FLOOKUP s.vs_labels l =
     OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (gvs[entry_bind_pairs_normal]) >>
  qexistsl_tac [`LENGTH (execute_plan cpl.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))`, `ast1`] >>
  conj_tac >- simp[execute_plan_def, exec_stack_op_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[active_frame_plan_def] >>
  qexistsl_tac [`i`, `r`, `liveness_analyze fn`, `dfg_build_function fn`,
    `cfg_analyze fn`,
    `cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
      unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name`,
    `cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context)`,
    `r.sr_spill_base`, `lbl_ctr`, `r.sr_plan`, `ps_end`, `HD fn.fn_blocks`,
    `init_cleanup_plan_state
      (cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
        unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name)
      (cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context))
      r.sr_spill_base lbl_ctr`,
    `(init_cleanup_plan_state
      (cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
        unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name)
      (cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context))
      r.sr_spill_base lbl_ctr).ps_cleanup_height`,
    `(init_cleanup_plan_state
      (cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
        unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name)
      (cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context))
      r.sr_spill_base lbl_ctr).ps_cleanup_promised`,
    `init_cleanup_plan_state
      (cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
        unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name)
      (cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context))
      r.sr_spill_base lbl_ctr`,
    `SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops`,
    `ps_after`, `ps_after`, `param_ops`, `body_ops`,
    `LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`, `ps1`,
    `ast.as_pc`, `pc_ret`] >>
  irule entry_body_plan >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> gvs[entry_bind_pairs_normal]
  >>
  FIRST [
    gen_tac >> disch_tac >>
      qpat_x_assum `!x. p x ==> normalize_operand d [] x = x`
        (qspec_then `at` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> simp[] >> NO_TAC,
    fs[fn_entry_state_rel_def] >> NO_TAC]
QED

Theorem entry_frame_plan_initial:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 ==>
  ?fn others lbl entry.
    unit.cu_context.ctx_functions = fn::others /\
    unit.cu_context.ctx_entry = SOME fn.fn_name /\
    fn_entry_label fn = SOME lbl /\
    entry = vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                       vs_inst_idx := 0 |> /\
    entry_frame_plan rpolicy unit cpl prog fn entry entry
      (entry_asm_state vs0 es0) 0w 0 []
      (entry_asm_state vs0 es0).as_memory
Proof
  strip_tac >>
  `?fn others. unit.cu_context.ctx_functions = fn::others /\
     unit.cu_context.ctx_entry = SOME fn.fn_name /\
     get_params (HD fn.fn_blocks).bb_instructions = []` by
    gvs[unit_shape_ok_def, entry_fn_first_def] >>
  `codegen_ready_fn fn` by
    fs[codegen_context_obligations_def, codegen_ready_def] >>
  `?lbl. fn_entry_label fn = SOME lbl` by
    (Cases_on `fn.fn_blocks` >>
     fs[codegen_ready_fn_def, venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  `fn_entry_state_rel cpl fn
    (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
    (entry_asm_state vs0 es0) 0w []` by
    metis_tac[entry_fn_entry_state_rel] >>
  `0 < LENGTH cpl.cp_regions` by
    metis_tac[fnPlanPlaceFnRegionTheory.context_region_leading_label,
      LENGTH, prim_recTheory.LESS_0, EL] >>
  `?r rs. cpl.cp_regions = r::rs` by
    (Cases_on `cpl.cp_regions` >> fs[]) >>
  `MEM fn.fn_name (fcg_analyze unit.cu_context).fcg_reachable` by
    (qspecl_then [`unit.cu_context`, `fn.fn_name`, `fn.fn_name`] mp_tac
      fcgAnalysisPropsTheory.fcg_analyze_reachable_complete >>
     simp[fcg_is_reachable_def, fcg_path_def, ctx_fn_names_def] >>
     fs[codegen_context_obligations_def]) >>
  `asm_block_at prog 0 (execute_plan cpl.cp_initial_fmp r.sr_plan)` by
    metis_tac[codegen_assembly_first_region] >>
  `!l. FLOOKUP vs0.vs_labels l =
    OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    fs[initial_ctx_rel_tail_def] >>
  qexistsl_tac [`fn`, `others`, `lbl`,
    `vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[] >> NO_TAC) >>
  mp_tac (Q.INST
    [`entry` |-> `vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0 |>`,
     `ast` |-> `entry_asm_state vs0 es0`, `ra` |-> `0w:bytes32`,
     `pc_ret` |-> `0`, `rest` |-> `[]:bytes32 list`,
     `i` |-> `0`, `r` |-> `r`]
    (SPEC_ALL entry_frame_plan_start)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      asm_simp_tac (srw_ss()) [entry_asm_state_def, fn_has_retpc_def]) >>
  simp[]
QED
