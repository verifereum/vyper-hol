(* The source parameter phase before its compiled entry packet executes. *)
Theory fnFramePrefixEntry
Ancestors
  codegenEntryFacts
  fnFramePrefix fnEntryParams fnEntryPlan fnEntryStep fnFrameBoundaryEntryParams
  codegenEntryRel fnBlockBodyHelpers fnBlockBodySteps
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

(* Label-map parameterization; the canonical definition above is retained. *)
Definition entry_frame_plan_reloc_def:
  entry_frame_plan_reloc lo rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 <=>
    generate_context_plan unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
    (!l. FLOOKUP entry.vs_labels l =
      OPTION_MAP n2w (FLOOKUP lo l)) /\
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

Theorem entry_frame_plan_reloc_specialize:
  entry_frame_plan_reloc (SND (compute_label_offsets prog))
    rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 <=>
  entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0
Proof
  simp[entry_frame_plan_reloc_def, entry_frame_plan_def]
QED

Theorem entry_frame_plan_start_reloc:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  (!l. FLOOKUP entry.vs_labels l =
    OPTION_MAP n2w (FLOOKUP lo l)) /\
  LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
  fn_entry_state_rel cpl fn entry ast ra rest /\
  (fn_has_retpc fn ==> FLOOKUP (build_offset_to_pc prog) (w2n ra) = SOME pc_ret) /\
  i < LENGTH unit.cu_context.ctx_functions /\
  EL i unit.cu_context.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
  MEM fn.fn_name (fcg_analyze unit.cu_context).fcg_reachable /\
  asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp r.sr_plan) ==>
  entry_frame_plan_reloc lo rpolicy unit cpl prog fn entry
    (entry with vs_inst_idx := 0) ast ra pc_ret rest ast.as_memory
Proof
  rw[entry_frame_plan_reloc_def] >- metis_tac[] >>
  qexists_tac `0` >> simp[entry_prefix_zero]
QED

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
  rewrite_tac[GSYM entry_frame_plan_reloc_specialize] >>
  metis_tac[entry_frame_plan_start_reloc]
QED

Theorem entry_frame_active_param_reloc:
  entry_frame_plan_reloc lo rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  active_inst fn inst s /\
  s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  inst = EL s.vs_inst_idx (get_params (HD fn.fn_blocks).bb_instructions) /\
  is_param_opcode inst.inst_opcode
Proof
  strip_tac >>
  qpat_x_assum `entry_frame_plan_reloc _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_frame_plan_reloc_def]) >>
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

Theorem entry_frame_active_param:
  entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  active_inst fn inst s /\
  s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  inst = EL s.vs_inst_idx (get_params (HD fn.fn_blocks).bb_instructions) /\
  is_param_opcode inst.inst_opcode
Proof
  rewrite_tac[GSYM entry_frame_plan_reloc_specialize] >>
  metis_tac[entry_frame_active_param_reloc]
QED

Theorem entry_frame_plan_next_reloc:
  entry_frame_plan_reloc lo rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  ?post.
    step_inst fuel unit.cu_context
      (EL s.vs_inst_idx (get_params (HD fn.fn_blocks).bb_instructions)) s = OK post /\
    entry_frame_plan_reloc lo rpolicy unit cpl prog fn entry
      (post with vs_inst_idx := SUC s.vs_inst_idx) ast ra pc_ret rest mem0
Proof
  strip_tac >>
  qpat_x_assum `entry_frame_plan_reloc _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_frame_plan_reloc_def]) >>
  `s.vs_inst_idx = k` by fs[] >>
  `codegen_ready_fn fn` by metis_tac[body_fn_shape] >>
  drule_all bounded_entry_param_shape >> strip_tac >>
  drule_all entry_prefix_step >> strip_tac >>
  qexists_tac `entry_bind_pairs
    (entry_param_pairs entry
      (TAKE (SUC k) (get_params (HD fn.fn_blocks).bb_instructions))) entry
      with vs_inst_idx := k` >>
  conj_tac >- metis_tac[] >>
  simp[entry_frame_plan_reloc_def] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `SUC k` >> fs[]
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
  rewrite_tac[GSYM entry_frame_plan_reloc_specialize] >>
  metis_tac[entry_frame_plan_next_reloc]
QED

Theorem entry_frame_plan_ready_reloc:
  entry_frame_plan_reloc lo rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  code_labels_agree prog lo /\
  s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  ?n ast1.
    0 < n /\
    asm_steps lo (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan_reloc lo rpolicy unit cpl prog fn s ast1 ra rest mem0
Proof
  strip_tac >>
  qpat_x_assum `entry_frame_plan_reloc _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_frame_plan_reloc_def]) >>
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
  `?ast1. asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan cpl.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) ast = AsmOK ast1 /\
    ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    fn_frame_inv unit.cu_context cpl lo fn ra rest ast.as_memory ps1 s ast1 /\
    create_safe_prefix lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan cpl.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) ast` by
    (irule entry_prefix_asm_exact_reloc >>
     simp[] >> metis_tac[LESS_EQ_REFL]) >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
     normalize_operand (dfg_build_function fn) [] at = at` by
    metis_tac[entry_plan_normalize] >>
  drule_at (Pat `codegen_context_obligations _ _ _`) codegen_invoke_targets_retpc >>
  simp[] >> strip_tac >>
  `!l. FLOOKUP s.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)` by
    gvs[entry_bind_pairs_normal] >>
  qexistsl_tac [`LENGTH (execute_plan cpl.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))`, `ast1`] >>
  conj_tac >- simp[execute_plan_def, exec_stack_op_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rewrite_tac[active_frame_plan_reloc_def] >>
  irule_at Any entry_body_plan_reloc >>
  simp[] >>
  qexistsl_tac [`ps_end`, `ps_after`, `ps1`, `pc_ret`, `ast.as_pc`,
    `param_ops`, `lbl_ctr`, `i`, `body_ops`] >>
  gvs[entry_bind_pairs_normal, APPEND] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- fs[fn_entry_state_rel_def] >>
  metis_tac[]
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
  rewrite_tac[GSYM entry_frame_plan_reloc_specialize,
              GSYM active_frame_plan_reloc_specialize] >>
  metis_tac[entry_frame_plan_ready_reloc,
    fnPlanPlaceRevertPostambleTheory.code_labels_agree_refl]
QED

Theorem entry_frame_plan_initial_reloc:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  code_labels_agree prog lo /\
  (!l. FLOOKUP vs0.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  (!fe rest lbl.
    unit.cu_context.ctx_functions = fe :: rest /\
    get_params (HD fe.fn_blocks).bb_instructions = [] /\
    fn_entry_label fe = SOME lbl ==>
    fn_entry_state_rel cpl fe
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
      (entry_asm_state vs0 es0) 0w []) ==>
  ?fn others lbl entry.
    unit.cu_context.ctx_functions = fn::others /\
    unit.cu_context.ctx_entry = SOME fn.fn_name /\
    fn_entry_label fn = SOME lbl /\
    entry = vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                       vs_inst_idx := 0 |> /\
    entry_frame_plan_reloc lo rpolicy unit cpl prog fn entry entry
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
    (entry_asm_state vs0 es0) 0w []` by metis_tac[] >>
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
  qexistsl_tac [`fn`, `others`, `lbl`,
    `vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`] >>
  simp[] >>
  irule (Q.INST [`entry` |->
    `vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`]
    entry_frame_plan_start_reloc |> SRULE []) >>
  simp[entry_asm_state_def, fn_has_retpc_def] >>
  qexists_tac `0` >> simp[]
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
  rewrite_tac[GSYM entry_frame_plan_reloc_specialize] >>
  strip_tac >>
  irule entry_frame_plan_initial_reloc >>
  simp[fnPlanPlaceRevertPostambleTheory.code_labels_agree_refl] >>
  conj_tac >- metis_tac[entry_fn_entry_state_rel_tail] >>
  fs[initial_ctx_rel_tail_def, initial_ctx_rel_def]
QED
