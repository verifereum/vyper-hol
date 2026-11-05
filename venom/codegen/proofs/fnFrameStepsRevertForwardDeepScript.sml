(*
 * revert_forward_frame_sim_deep: fnFrameSteps' revert_forward_frame_sim
 * for a planner state with cleanup markers.  A cleanup elision
 * (clean_stack_plan's mark_dead_stack) leaves dead_stack_marker in several
 * stack slots, so the block induction keeps generated_plan_state_wf_marked
 * (fnPlanPrefix), not generated_plan_state_wf.  The other fnFrameDeep
 * relaxations don't apply: revert_forward_frame_sim's ownership premise
 * already allows any depth, and it has no prefix_spill_wf premise (its
 * plan has no SOSpill or SORestore at all).
 *
 * TOP-LEVEL:
 *   revert_forward_frame_sim_deep
 *)

Theory fnFrameStepsRevertForwardDeep
Ancestors
  contextCodegenRel dfgDefs list dfgAnalysisProps allocaRemapSSA venomWf
  stackPlanGen venomExecProofs removeUnusedSsaProofs frameRel
  frameViewFacts instSimHelpers emitSim venomExecSemantics venomInst
  strongPrefixSim asmFrameHelpers planExec prefixExec stackOpAsmSim
  stackOpSim blockSimHelpers asmSem stackModel rich_list codegenRel planWf
  reorderSim genBlockSim doSwapSim planAlign livenessAnalysisProps stackPlanOps
  fnFrameTerminalHalt fnFrameTerminalAbort genericInputReady
  fnFrameStepsRevertForward fnPlanPrefix

(* fnFrameStepsRevertForward's entry lemmas use generated_plan_state_wf
   only for spill separation (rf_spills_separated_entry), which the marked
   invariant gives as well.  These are those lemmas with rf_spills_separated
   as the premise instead. *)
Theorem rf_spills_separated_entry_marked:
  !base ps. generated_plan_state_wf_marked base ps ==> rf_spills_separated ps
Proof
  rpt strip_tac >> fs[generated_plan_state_wf_marked_def] >>
  drule spill_alloc_layout_wf_spilled_separated >>
  simp[rf_spills_separated_def]
QED

Theorem rf_entry_copy_execution_sep:
  codegen_ready_fn fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  if w2n src + w2n sz <= LENGTH vs.vs_returndata then
  (?st' stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk' /\
    venom_asm_terminal_rel vs' st' /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) st'.as_memory))
  else
  (?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmFault st' /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) st')
Proof
  strip_tac >>
  `rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs` by
    (irule rf_inventory_inv_entry >> first_assum ACCEPT_TAC) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >> irule rf_inventory_inv_input_value >>
     qexists_tac `ps` >> simp[]) >>
  drule_all rf_suffix_copy_execution >> simp[]
QED


Theorem rf_entry_copy_setup_sep:
  !ctx cp lo prog liveness dfg cfg fn bb i j ps vs ast ops
   ps_end ra rest mem0.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ rf_spills_separated ps /\
    (!k inst op. i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    ?inst dop sop zop dst src sz step_ops rest_ops ps1 stk.
      lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ i < j /\
      get_instruction bb i = SOME inst /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
      inst.inst_operands = [dop;sop;zop] /\
      EVERY (\op. ~is_label_operand op) inst.inst_operands /\
      operand_val (frame_view fn ra vs) lo dop = SOME dst /\
      operand_val (frame_view fn ra vs) lo sop = SOME src /\
      operand_val (frame_view fn ra vs) lo zop = SOME sz /\
      (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      rf_spills_separated ps /\
      rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs /\
      rf_value_inv fn ra bb j lo (frame_view fn ra vs) i vs /\
      (!op. rf_live_use bb i j op /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      ast.as_stack = stk ++ rest /\
      plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
      venom_asm_terminal_rel vs ast /\ ops = step_ops ++ rest_ops /\
      generate_regular_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (SUC i)) (bb_is_halting bb)
        (case DROP (SUC i) bb.bb_instructions of
           [] => F | next_i :: _ => is_terminator next_i.inst_opcode)
        bb.bb_label ps = (step_ops,ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (SUC i - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC i) bb.bb_instructions) ps1 = SOME (rest_ops,ps_end) /\
      (!off. ~MEM (SORestore off) step_ops /\ ~MEM (SOSpill off) step_ops /\
             ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) /\
      asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp step_ops) /\
      asm_block_at prog (ast.as_pc + LENGTH (execute_plan cp.cp_initial_fmp step_ops))
        (execute_plan cp.cp_initial_fmp rest_ops)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    metis_tac[makeSsaHelperTheory.lookup_block_label] >>
  `i < j` by fs[revert_forward_pair_def] >>
  `i <= i /\ i <= j` by decide_tac >>
  `?inst. get_instruction bb i = SOME inst` by
    (irule rf_forward_instruction_exists >> qexistsl_tac [`i`, `j`] >> simp[]) >>
  `inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
   LENGTH inst.inst_operands = 3` by
    (drule_all rf_forward_instruction_shape >> strip_tac >>
     drule_all rf_forward_instruction_opcode >> simp[]) >>
  `?dop sop zop. inst.inst_operands = [dop;sop;zop]` by
    fs[listTheory.LENGTH_EQ_NUM_compute] >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule rf_suffix_instruction_no_labels >> metis_tac[]) >>
  `rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs` by
    (irule rf_inventory_inv_entry >> gvs[]) >>
  `!op. rf_live_use bb i j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> fs[rf_live_use_def] >> first_x_assum irule >> metis_tac[]) >>
  `rf_value_inv fn ra bb j lo (frame_view fn ra vs) i vs` by
    (irule rf_value_inv_entry >>
     qexists_tac `\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` >>
     gvs[] >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all rf_block_plan_step >> strip_tac >>
  `generate_regular_inst_plan liveness dfg cfg fn inst
    (live_vars_at liveness bb.bb_label (SUC i)) (bb_is_halting bb)
    (case DROP (SUC i) bb.bb_instructions of
       [] => F | next_i :: _ => is_terminator next_i.inst_opcode)
    bb.bb_label ps = (step_ops,ps1)` by
    (irule rf_forward_regular_plan_result >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`, `i`, `j`, `i`] >> simp[]) >>
  `?stk. ast.as_stack = stk ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk` by
    (qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[frameRelTheory.fn_frame_inv_def, contextCodegenRelTheory.context_venom_asm_rel_def] >>
     metis_tac[]) >>
  `venom_asm_terminal_rel vs ast` by
    (fs[frameRelTheory.fn_frame_inv_def, contextCodegenRelTheory.context_venom_asm_rel_def,
        venom_asm_terminal_rel_def, frameRelTheory.frame_view_def]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule rf_live_use_current >> simp[] >> qexists_tac `inst` >> simp[]) >>
  `!op. MEM op inst.inst_operands ==>
    ?v. operand_val (frame_view fn ra vs) lo op = SOME v` by
    (rpt strip_tac >> irule rf_frame_input_defined >>
     conj_tac >- gvs[EVERY_MEM] >>
     qexistsl_tac [`cp'`, `ctx`, `mem0`, `ps`, `rest`, `ast`] >>
     asm_rewrite_tac[] >>
     strip_tac >> first_x_assum irule >>
     gvs[compute_operands_def, python_stack_operands_def,
         venomInstTheory.ir_specific_operand_order_def]) >>
  `?dst src sz.
    operand_val (frame_view fn ra vs) lo dop = SOME dst /\
    operand_val (frame_view fn ra vs) lo sop = SOME src /\
    operand_val (frame_view fn ra vs) lo zop = SOME sz` by
    metis_tac[listTheory.MEM] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
     qexists_tac `bb` >> conj_tac >- metis_tac[lookup_block_MEM] >>
     gvs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  qexistsl_tac [`inst`, `dop`, `sop`, `zop`, `dst`, `src`, `sz`,
    `step_ops`, `rest_ops`, `ps1`, `stk`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  fs[execute_plan_append, asm_block_at_append]
QED

Theorem rf_entry_forward_abort_sep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j ps vs ast ops
   ps_end ra rest mem0 a vs_end.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ rf_spills_separated ps /\
    (!k inst op. i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    exec_block fuel ctx bb vs = Abort a vs_end ==>
    ?n ast_end.
      ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
       (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
      venom_asm_terminal_rel vs_end ast_end
Proof
  rpt gen_tac >> strip_tac >>
  drule_all rf_entry_copy_setup_sep >> strip_tac >>
  drule_all rf_copy_source_alignment >> disch_then (assume_tac o GSYM) >>
  Cases_on `emit_input_plan RETURNDATACOPY (compute_operands inst)
    (live_vars_at liveness bb.bb_label (SUC i)) ps` >>
  rename1 `_ = (ins,prep)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) prep` >>
  rename1 `_ = (ros,arr)` >>
  qpat_x_assum `liveness = _` SUBST_ALL_TAC >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!k inst op. _` kall_tac >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ (DROP i _) _ = _` kall_tac >>
  qabbrev_tac `copy = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs` >>
  `copy = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs` by simp[Abbr `copy`] >>
  `!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops` by
    (qpat_x_assum `!off. _ /\ _ /\ _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule_all rf_entry_copy_execution_sep >>
  disch_then (qspec_then `o2pc` mp_tac) >>
  reverse (Cases_on `w2n src + w2n sz <= LENGTH vs.vs_returndata`) >>
  pure_asm_rewrite_tac[COND_CLAUSES] >> strip_tac
  >- (`a = ExHalt_abort /\ vs_end = halt_state (set_returndata [] vs)` by
        (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
         qpat_x_assum `!fuel ctx. _ = step_inst _ _ _ _` mp_tac >>
         qpat_x_assum `get_instruction bb i = _` mp_tac >>
         qpat_x_assum `vs.vs_inst_idx = i` mp_tac >>
         qpat_x_assum `~(w2n src + w2n sz <= _)` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         qpat_x_assum `!fuel ctx. _ = step_inst _ _ _ _`
           (assume_tac o GSYM) >>
         gvs[Once exec_block_def]) >>
      metis_tac[]) >>
  `step_inst fuel ctx inst vs = OK copy` by
    (qpat_x_assum `!fuel ctx. _ = step_inst _ _ _ _` mp_tac >>
     qpat_x_assum `w2n src + w2n sz <= _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `exec_block fuel ctx bb (copy with vs_inst_idx := SUC i) = Abort a vs_end` by
    (qpat_x_assum `exec_block fuel ctx bb vs = _` mp_tac >>
     qpat_x_assum `step_inst fuel ctx inst vs = OK copy` mp_tac >>
     qpat_x_assum `get_instruction bb i = _` mp_tac >>
     qpat_x_assum `vs.vs_inst_idx = i` mp_tac >>
     qpat_x_assum `inst.inst_opcode = RETURNDATACOPY` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[Once exec_block_def, is_terminator_def]) >>
  `LENGTH (compute_operands inst) <= 16` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  `!r ti. SUC i <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
     ti.inst_opcode <> PHI` by
    (rpt strip_tac >> `i <= r` by decide_tac >>
     drule_all rf_forward_instruction_opcode >>
     simp[] >> rpt IF_CASES_TAC >> simp[]) >>
  `i <= j` by decide_tac >>
  drule_all rf_suffix_copy_success_invariants >> strip_tac >>
  `operand_val (frame_view fn ra vs) lo
     (normalize_operand (dfg_build_function fn) [] dop) = SOME dst /\
   operand_val (frame_view fn ra vs) lo
     (normalize_operand (dfg_build_function fn) [] zop) = SOME sz` by
    (qpat_x_assum `rf_value_inv _ _ _ _ _ _ i vs` mp_tac >>
     simp[rf_value_inv_def] >> strip_tac >>
     `rf_live_use bb i j dop /\ rf_live_use bb i j zop` by
       (conj_tac >> (irule rf_live_use_current >>
        (conj_tac >- decide_tac) >> qexists_tac `inst` >>
        simp[compute_operands_def, python_stack_operands_def,
          ir_specific_operand_order_def])) >>
     metis_tac[]) >>
  `i < SUC i /\ SUC i <= j /\ LENGTH (get_params bb.bb_instructions) <= SUC i` by decide_tac >>
  `!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops` by
    (qpat_x_assum `!off. _ /\ _ /\ _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `asm_block_at prog st'.as_pc (execute_plan cp'.cp_initial_fmp rest_ops)` by
    metis_tac[] >>
  `plan_stack_rel lo (frame_view fn ra (copy with vs_inst_idx := SUC i)) ps1.ps_stack stk' /\
   venom_asm_terminal_rel (copy with vs_inst_idx := SUC i) st' /\
   TAKE (w2n sz) (DROP (w2n dst) (copy with vs_inst_idx := SUC i).vs_memory) =
     TAKE (w2n sz) (DROP (w2n dst) st'.as_memory)` by
    (qpat_x_assum `copy = write_memory_with_expansion _ _ _` SUBST_ALL_TAC >>
     qpat_x_assum `plan_stack_rel _ _ ps1.ps_stack _` mp_tac >>
     qpat_x_assum `venom_asm_terminal_rel (write_memory_with_expansion _ _ _) _` mp_tac >>
     qpat_x_assum `TAKE _ (DROP _ _.vs_memory) = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venom_asm_terminal_rel_def, codegenRelTheory.plan_stack_rel_def,
       frame_view_def] >> rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH ps1.ps_stack ==> _`
       (qspec_then `i'` mp_tac) >> simp[] >>
     Cases_on `EL i' (REVERSE ps1.ps_stack)` >>
     simp[codegenRelTheory.operand_val_def, venomStateTheory.lookup_var_def]) >>
  `(copy with vs_inst_idx := SUC i).vs_inst_idx = SUC i` by simp[] >>
  drule_all rf_strict_suffix_abort >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexistsl_tac [`LENGTH (execute_plan cp'.cp_initial_fmp step_ops) + n`, `out`] >>
  simp[] >>
  qpat_x_assum `asm_steps _ _ _ _ ast = AsmOK _`
    (mp_then Any (qspec_then `n` mp_tac) asm_steps_add_ok) >>
  simp[]
QED

(* Used in the block induction at a revert forwarding's RETURNDATACOPY, as
   revert_forward_frame_sim, from the planner state the induction keeps.

   Why it should hold: as revert_forward_frame_sim.  The segment's code
   has no spill or restore, so the spill map is only read through
   fn_frame_inv; generated_plan_state_wf's ALL_DISTINCT ps_stack is only
   needed to find an operand's stack slot, and stack_get_depth finds the
   topmost copy whatever the marker slots below it, which hold no
   variable and are never an operand (dead_stack_marker is no operand of
   a codegen_ready_fn instruction). *)
Theorem revert_forward_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j base ps vs as ops
   ps_end ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\
    generated_plan_state_wf_marked base ps /\
    (!k inst op.
       i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as'
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  drule rf_spills_separated_entry_marked >> strip_tac >>
  drule_all rf_entry_forward_abort_sep >> simp[]
QED
