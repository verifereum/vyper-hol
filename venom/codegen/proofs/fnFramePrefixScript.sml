(* Active codegen frames at finite cuts of the actual execution. *)
Theory fnFramePrefix
Ancestors
  fnBlockBody fnBlockBodyClasses fnBlockBodySteps fnBlockBodyHelpers fnEntryStep
  fnEntryPlan fnEntryParams fnBlockStepHelpers fnPlanLineage asmFrameRun
  asmFrameLocalStep unitMemInv
  blockSimHelpers gasFrameSim frameRel stackPlanTypes planExec asmSem stackOpSim
  contextCodegenRel codegenRel venomExecProps venomExecSemantics venomExecProofs venomInst venomState
  stackPlanGen unitShapeDefs list rich_list arithmetic

(* Only the active planner/frame facts are existentially packaged here. *)
Definition active_frame_plan_def:
  active_frame_plan rpolicy unit cpl prog fn s a ra rest mem0 <=>
    ?i r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
     bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
     rest_ops k ps pc0 pc_ret.
      body_plan_inv rpolicy unit cpl prog unit.cu_context
        (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        i fn r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
        bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
        rest_ops k ps pc0 s a ra pc_ret rest mem0
End

Theorem entry_body_plan:
  !rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   lbl_ctr ps_end ps0 param_ops ps1 body_ops ps_after pc_bb vs as
   ra pc_ret rest mem0.
  ctx = unit.cu_context /\ lo = SND (compute_label_offsets prog) /\
  o2pc = build_offset_to_pc prog /\ generate_context_plan ctx = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
  EL i cpl.cp_regions = r /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  (!f inst callee_name args callee.
    MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
    MEM inst (fn_insts f) /\
    inst.inst_opcode = INVOKE /\ inst.inst_operands = Label callee_name :: args /\
    lookup_function callee_name ctx.ctx_functions = SOME callee ==>
    fn_has_retpc callee) /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  codegen_context_obligations (\_ _ _ _. F) ctx cpl /\

  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\
  ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
         (fcg_analyze ctx) fn.fn_name /\
  growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
  ps0 = init_cleanup_plan_state ch growth r.sr_spill_base lbl_ctr /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    r.sr_spill_base lbl_ctr = SOME (r.sr_plan, ps_end) /\
  ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label /\
  vs.vs_current_bb = (HD fn.fn_blocks).bb_label /\
  lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks = SOME (HD fn.fn_blocks) /\
  dfs_block_state liveness dfg cfg fn ps0 (HD fn.fn_blocks).bb_label ps0 /\
  generate_block_plan liveness dfg cfg fn (HD fn.fn_blocks) ps0 =
    SOME (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops, ps_after) /\
  block_plan_state liveness dfg cfg fn (HD fn.fn_blocks) ps0
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1 /\
  generate_block_insts_plan liveness dfg cfg fn (HD fn.fn_blocks).bb_label
    (bb_is_halting (HD fn.fn_blocks))
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
    (LENGTH (HD fn.fn_blocks).bb_instructions) 0
    (non_param_insts (HD fn.fn_blocks)) ps1 = SOME (body_ops, ps_after) /\
  vs.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
  asm_block_at prog pc_bb (execute_plan cpl.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
  as.as_pc = pc_bb + LENGTH (execute_plan cpl.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps1 vs as /\
  (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
  (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) ==>
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth r.sr_spill_base lbl_ctr r.sr_plan ps_end (HD fn.fn_blocks) ps0
    ps0.ps_cleanup_height ps0.ps_cleanup_promised ps0
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)
    ps_after ps_after param_ops body_ops
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1 pc_bb
    vs as ra pc_ret rest mem0
Proof
  rpt gen_tac >> strip_tac >>
  `codegen_ready_fn fn` by metis_tac[body_fn_shape] >>
  `fn_reachable fn (HD fn.fn_blocks).bb_label` by
    (simp[venomWfTheory.fn_reachable_def] >>
     metis_tac[relationTheory.RTC_REFL]) >>
  drule entry_step_phi_bound >> strip_tac >>
  `lineage_state liveness dfg cfg fn ps0 (HD fn.fn_blocks).bb_label ps0` by
    metis_tac[lineage_state_rules] >>
  `!i j. revert_forward_pair (HD fn.fn_blocks) i j ==>
         LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <= i \/
         j < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    metis_tac[revert_forward_pair_past_params] >>
  PURE_REWRITE_TAC [body_plan_inv_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  gvs[init_cleanup_plan_state_def, init_plan_state_def] >>
  qexistsl_tac [`[]`, `[]`, `ps_after.ps_stack`] >> simp[]
QED

Theorem body_plan_gas_ready:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast
      ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = GAS ==>
  ast.as_pc < LENGTH prog /\ EL ast.as_pc prog = AsmOp "GAS" /\
  ast.as_gas_readings = vs.vs_gas_readings
Proof
  strip_tac >> drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all gas_source_shape >> strip_tac >>
  `generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k+1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k+1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps =
    SOME (if MEM out (live_vars_at liveness bb.bb_label (k+1)) then
      case optimistic_swap_plan dfg inst
        (live_vars_at liveness bb.bb_label (k+1))
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k+1) bb.bb_instructions).inst_opcode)
        (ps with ps_stack := SNOC (Var out) ps.ps_stack) of
        (tail, ps9) => (SOEmit "GAS" :: tail,
          release_dead_spills (live_vars_at liveness bb.bb_label (k+1)) ps9)
    else if bb_is_halting bb then
      ([SOEmit "GAS"], release_dead_spills
        (live_vars_at liveness bb.bb_label (k+1))
        (ps with ps_stack := SNOC (Var out) ps.ps_stack))
    else ([SOEmit "GAS"; SOPop 1],
      release_dead_spills (live_vars_at liveness bb.bb_label (k+1)) ps))` by
    (irule gas_plan_shape >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?tail. ops = SOEmit "GAS" :: tail` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME (if _ then _ else _)`
       (fn shape =>
        qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME (ops, ps')`
          (fn actual => mp_tac (TRANS (SYM actual) shape))) >>
     Cases_on `MEM out (live_vars_at liveness bb.bb_label (k+1))`
     >- (simp[] >> Cases_on `optimistic_swap_plan dfg inst
       (live_vars_at liveness bb.bb_label (k+1))
       (k + 1 < LENGTH bb.bb_instructions /\
        is_terminator (EL (k+1) bb.bb_instructions).inst_opcode)
       (ps with ps_stack := SNOC (Var out) ps.ps_stack)` >> simp[] >>
       strip_tac >> gvs[]) >>
     Cases_on `bb_is_halting bb` >> simp[] >> strip_tac >> gvs[]) >>
  `asm_block_at prog ast.as_pc
     (AsmOp "GAS" :: execute_plan cpl.cp_initial_fmp tail)` by
    gvs[execute_plan_def, exec_stack_op_def] >>
  gvs[asm_block_at_cons] >>
  fs[body_plan_inv_def] >> metis_tac[fn_frame_inv_gas_readings]
QED

Theorem body_plan_active_inst:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast
      ra pc_ret rest mem0 /\ active_inst fn inst vs ==>
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst
Proof
  strip_tac >> drule body_plan_inv_facts >> strip_tac >>
  `wf_function fn` by fs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `vs.vs_inst_idx = k` by fs[body_plan_inv_def] >>
  fs[active_inst_def] >>
  `bb = bb'` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[]
QED

Theorem active_frame_gas_ready:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ inst.inst_opcode = GAS ==>
  ast.as_pc < LENGTH prog /\ EL ast.as_pc prog = AsmOp "GAS" /\
  ast.as_gas_readings = vs.vs_gas_readings
Proof
  rw[active_frame_plan_def] >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_gas_ready >> simp[]
QED

Theorem active_frame_gas_available:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ inst.inst_opcode = GAS /\
  asm_frame_prog_ok prog /\ asm_frame_rel tail prog data es0 ast es /\
  run_call es = SOME (r,es') /\ ~frame_resource_starved es0 r es' ==>
  LENGTH tail < LENGTH vs.vs_gas_readings
Proof
  strip_tac >> drule_all active_frame_gas_ready >> strip_tac >>
  `~is_data_inst (EL ast.as_pc prog)` by simp[asmWfTheory.is_data_inst_def] >>
  drule_all asm_frame_gas_step >> strip_tac >- gvs[] >>
  fs[asmFrameRelTheory.asm_frame_rel_def]
QED

Theorem active_frame_gas_pop:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ inst.inst_opcode = GAS /\
  asm_frame_prog_ok prog /\ asm_frame_rel tail prog data es0 ast es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es0 result final ==>
  ?es1 w a1.
    step es = (INL (),es1) /\ run_call es1 = SOME (result,final) /\
    gas_readings es = w::gas_readings es1 /\
    vs.vs_gas_readings = w::(gas_readings es1 ++ tail) /\
    asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      (AsmOp "GAS") ast = AsmOK a1 /\
    asm_frame_rel tail prog data es0 a1 es1
Proof
  strip_tac >> drule_all active_frame_gas_ready >> strip_tac >>
  `~is_data_inst (EL ast.as_pc prog)` by simp[asmWfTheory.is_data_inst_def] >>
  drule_all asm_frame_gas_step >> strip_tac >- gvs[] >>
  qexistsl_tac [`es1`, `w`, `a1`] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> fs[asmFrameRelTheory.asm_frame_rel_def]
QED

val active_plan_witnesses =
  [`i`, `r`, `liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`,
   `lbl_ctr`, `fn_ops`, `ps_end`, `bb`, `ps_l`, `h`, `promised`, `ps_dfs`,
   `block_ops`, `ps_dfs_after`, `ps_after`, `prefix_ops ++ ops`, `rest'`,
   `SUC k`, `ps'`, `pc0`, `pc_ret`];

Theorem active_frame_ordinary_step:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ ~in_revert_forward fn vs /\
  source_memory_reads_disjoint cpl inst vs /\
  context_source_memory_writes_disjoint cpl inst vs /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ~is_terminator inst.inst_opcode /\
  step_inst fuel unit.cu_context inst vs = OK vs1 ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn
      (vs1 with vs_inst_idx := SUC vs.vs_inst_idx) ast1 ra rest mem0
Proof
  rw[active_frame_plan_def] >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  `vs.vs_inst_idx = k` by fs[body_plan_inv_def] >>
  `!j. ~revert_forward_pair bb k j` by
    (fs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  drule_all body_operands_le_16 >> strip_tac >>
  `(inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4)` by
    (strip_tac >> drule_all body_log_topics >> Cases_on `inst.inst_operands` >> simp[] >>
     Cases_on `h'` >> simp[] >> metis_tac[]) >>
  drule_all body_plan_ordinary_ok >> strip_tac >>
  drule_all body_plan_advance >> strip_tac >>
  qexistsl_tac [`n`, `as1`] >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[active_frame_plan_def] >> qexistsl_tac active_plan_witnesses >>
  gvs[]
QED

Theorem active_frame_gas_step:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ ~in_revert_forward fn vs /\
  inst.inst_opcode = GAS /\
  step_inst fuel unit.cu_context inst vs = OK vs1 ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn
      (vs1 with vs_inst_idx := SUC vs.vs_inst_idx) ast1 ra rest mem0
Proof
  rw[active_frame_plan_def] >>
  `source_memory_reads_disjoint cpl inst vs /\
   context_source_memory_writes_disjoint cpl inst vs` by
    simp[source_memory_reads_disjoint_def, context_source_memory_writes_disjoint_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  `vs.vs_inst_idx = k` by fs[body_plan_inv_def] >>
  `!j. ~revert_forward_pair bb k j` by
    (fs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  drule_all body_operands_le_16 >> strip_tac >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  drule_all body_plan_gas_ok >> strip_tac >>
  drule_all body_plan_advance >> strip_tac >>
  qexistsl_tac [`n`, `as1`] >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[active_frame_plan_def] >> qexistsl_tac active_plan_witnesses >>
  gvs[]
QED

Theorem active_frame_total_step:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ ~in_revert_forward fn vs /\
  (inst.inst_opcode = GAS \/ inst.inst_opcode = ASSIGN) /\
  step_inst fuel unit.cu_context inst vs = OK vs1 ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn
      (vs1 with vs_inst_idx := SUC vs.vs_inst_idx) ast1 ra rest mem0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (drule_all active_frame_gas_step >> simp[]) >>
  `inst.inst_opcode = ASSIGN` by fs[] >>
  `source_memory_reads_disjoint cpl inst vs /\
   context_source_memory_writes_disjoint cpl inst vs /\
   inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by
    simp[source_memory_reads_disjoint_def, context_source_memory_writes_disjoint_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def, is_terminator_def] >>
  drule_all active_frame_ordinary_step >> simp[]
QED

Theorem active_frame_static_step:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ ~in_revert_forward fn vs /\
  static_mem_ok cpl.cp_max_static_eom unit.cu_context fn inst vs /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel unit.cu_context inst vs = OK vs1 ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn
      (vs1 with vs_inst_idx := SUC vs.vs_inst_idx) ast1 ra rest mem0
Proof
  strip_tac >>
  `generate_context_plan unit.cu_context = SOME cpl` by
    fs[active_frame_plan_def, body_plan_inv_def] >>
  drule contextPlanLayoutPropsTheory.generate_context_plan_spill_gap >> strip_tac >>
  drule_all static_mem_ok_codegen_disjoint >> strip_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- (drule_all active_frame_gas_step >> simp[]) >>
  drule_all active_frame_ordinary_step >> simp[]
QED

Theorem body_plan_jump_next:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast
      ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to target vs /\
  MEM target (get_successors inst) /\
  asm_steps lo o2pc prog n ast = AsmOK amid /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 amid /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
     operand_val (frame_view fn ra vs1) lo at =
     operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo target = SOME off /\ FLOOKUP o2pc off = SOME amid.as_pc /\
  enters_block fn vs1 s1 ==>
  ?m ast1.
    asm_steps lo o2pc prog m amid = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn s1 ast1 ra rest mem0
Proof
  strip_tac >> drule_all body_plan_jump_entry >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  `bb.bb_label = vs.vs_current_bb /\ vs.vs_inst_idx = k` by
    fs[body_plan_inv_def] >>
  `vs1.vs_current_bb = target /\ vs1.vs_prev_bb = SOME bb.bb_label /\
   vs1.vs_labels = vs.vs_labels /\ vs1.vs_call_ctx = vs.vs_call_ctx` by
    simp[jump_to_def] >>
  `?s_phi. eval_phis vs1 tbb.bb_instructions = OK s_phi /\
           s1 = s_phi with vs_inst_idx := phi_prefix_length tbb.bb_instructions` by
    fs[enters_block_def] >>
  `s_phi.vs_labels = vs1.vs_labels /\
   s_phi.vs_current_bb = vs1.vs_current_bb /\
   s_phi.vs_call_ctx = vs1.vs_call_ctx` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  first_assum (strip_assume_tac o REWRITE_RULE [body_plan_inv_def] o
    assert (fn th => fst (dest_const (fst (strip_comb (concl th)))) =
                     "body_plan_inv")) >>
  qabbrev_tac `entry_plan = ps_tdfs with
    <| ps_stack := ps_after.ps_stack; ps_spilled := ps_after.ps_spilled |>` >>
  qspecl_then [`unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `i`, `fn`, `r`,
    `liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`, `lbl_ctr`,
    `fn_ops`, `ps_end`, `tbb`, `bb.bb_label`, `entry_plan`, `ps_tdfs`,
    `tops`, `tafter`, `vs1`, `amid`, `\_ _ _ _. F`, `ra`, `rest`, `mem0`,
    `s_phi`] mp_tac block_step_prefix >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              simp[Abbr `entry_plan`] >> gvs[]) >>
  disch_then (qx_choosel_then [`h_next`, `promised_next`, `pa_next`,
    `prefix_next`, `rest_next`, `ps_next`, `m`, `ast1`] strip_assume_tac) >>
  `lineage_state liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr)
     tbb.bb_label entry_plan` by
    (irule lineage_entry_lineage_state >> simp[Abbr `entry_plan`] >> metis_tac[]) >>
  `!a b. revert_forward_pair tbb a b ==>
         phi_prefix_length tbb.bb_instructions <= a \/
         b < phi_prefix_length tbb.bb_instructions` by
    metis_tac[revert_forward_pair_past_phis] >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`ctx = unit.cu_context`, `lo = SND (compute_label_offsets prog)`,
     `o2pc = build_offset_to_pc prog`,
     `liveness = liveness_analyze fn`, `dfg = dfg_build_function fn`,
     `cfg = cfg_analyze fn`, `ch = _`, `growth = _`, `spill_base = _`] >>
  qexistsl_tac [`m`, `ast1`] >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[active_frame_plan_def] >>
  qexistsl_tac [`i`, `r`, `liveness_analyze fn`, `dfg_build_function fn`,
    `cfg_analyze fn`,
    `cleanup_caller_height (LENGTH unit.cu_context.ctx_functions) unit.cu_context
      (fcg_analyze unit.cu_context) fn.fn_name`,
    `cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context)`,
    `r.sr_spill_base`, `lbl_ctr`, `fn_ops`, `ps_end`, `tbb`, `entry_plan`,
    `h_next`, `promised_next`, `ps_tdfs`, `tops`, `tafter`, `pa_next`,
    `prefix_next`, `rest_next`, `phi_prefix_length tbb.bb_instructions`,
    `ps_next`, `amid.as_pc`, `pc_ret`] >>
  PURE_REWRITE_TAC [body_plan_inv_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> asm_simp_tac (srw_ss()) []
  >>
  qexistsl_tac [`prefixL'`, `prefixD'`, `core'`] >>
  simp[] >> metis_tac[]
QED

Theorem active_frame_jump_step:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ is_terminator inst.inst_opcode /\
  step_inst fuel unit.cu_context inst vs = OK vs1 /\
  enters_block fn vs1 s1 ==>
  ?n ast1.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn s1 ast1 ra rest mem0
Proof
  strip_tac >>
  qpat_x_assum `active_frame_plan _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [active_frame_plan_def]) >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_operands_le_16 >> strip_tac >>
  `inst.inst_opcode <> DJMP` by fs[unitShapeDefsTheory.inst_shape_ok_def] >>
  `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ` by
    metis_tac[step_ok_terminator_jump] >>
  `?target n amid off.
    0 < n /\ vs1 = jump_to target vs /\ MEM target (get_successors inst) /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK amid /\
    fn_frame_inv unit.cu_context cpl (SND (compute_label_offsets prog))
      fn ra rest mem0 ps_after vs1 amid /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
       operand_val (frame_view fn ra vs1) (SND (compute_label_offsets prog)) at =
       operand_val (frame_view fn ra vs1) (SND (compute_label_offsets prog))
         (normalize_operand dfg [] at)) /\
    FLOOKUP (SND (compute_label_offsets prog)) target = SOME off /\
    FLOOKUP (build_offset_to_pc prog) off = SOME amid.as_pc` by
    (Cases_on `inst.inst_opcode = JMP`
     >- (drule_all body_plan_jmp_step >> fs[])
     >> `inst.inst_opcode = JNZ` by fs[] >>
     drule_all body_plan_jnz_step >> fs[]) >>
  drule_all body_plan_jump_next >>
  disch_then (qx_choosel_then [`next_n`, `next_as`] strip_assume_tac) >>
  qexistsl_tac [`n + next_n`, `next_as`] >> rpt conj_tac >> TRY decide_tac >>
  FIRST [first_assum ACCEPT_TAC,
    irule asm_steps_compose_ok >> qexists_tac `amid` >>
    conj_tac >> first_assum ACCEPT_TAC]
QED

Theorem active_frame_block_rank:
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs ==>
  ?bb. lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    vs.vs_inst_idx < LENGTH bb.bb_instructions /\
    LENGTH bb.bb_instructions - SUC vs.vs_inst_idx <
      LENGTH bb.bb_instructions - vs.vs_inst_idx
Proof
  rw[active_frame_plan_def] >>
  drule_all body_plan_active_inst >> strip_tac >>
  `lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
   vs.vs_inst_idx = k` by fs[body_plan_inv_def] >>
  qexists_tac `bb` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac
QED
