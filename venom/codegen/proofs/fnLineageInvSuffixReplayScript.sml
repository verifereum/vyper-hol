Theory fnLineageInvSuffixReplay
Ancestors fnLineageInvActualReplay fnLineageInvOrdinarySuffix fnLineageInvBoundary
  fnLineageInvSupport fnPlanLineageCallers fnPlanLineagePath
  fnPlanLineageStages fnPlanLineageInventory reorderSim stackPlanGen
  venomWf venomInst list rich_list pred_set

Theorem analyzed_ordinary_inst_bottom_frame:
 !fn bb k dfg cfg term base ps ops qs m.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 k < LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI) (DROP k bb.bb_instructions) /\
 (EL k bb.bb_instructions).inst_opcode <> JMP /\
 ~is_param_opcode (EL k bb.bb_instructions).inst_opcode /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k))) ps /\
 (?n core. lineage_core n core ps /\ residual_budget_wf base [] (ps with ps_stack := core)) /\
 generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
   (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label ps = SOME (ops,qs)
 ==>
 generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
   (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label
   (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
 SOME (ops, qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >> strip_tac >>
 `(EL k bb.bb_instructions).inst_opcode <> PHI` by
   (gvs[EVERY_MEM] >> first_x_assum irule >> simp[MEM_DROP, MEM_EL] >> qexists_tac `0` >> simp[]) >>
 Cases_on `(EL k bb.bb_instructions).inst_opcode = NOP`
 >- (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
 Cases_on `(EL k bb.bb_instructions).inst_opcode = OFFSET`
 >- suspend "offset" >>
 drule_all lineage_inventory_canonical_budget >> strip_tac >>
 `ps.ps_stack = REPLICATE n' dead_stack_marker ++ tail` by gvs[lineage_core_def] >>
 `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
   (drule lineage_inventory_live_membership >> simp[]) >>
 `!v. MEM (Var v) (compute_operands (EL k bb.bb_instructions)) ==>
    MEM (Var v) tail \/ Var v IN FDOM ps.ps_spilled` by
   (rpt strip_tac >>
    `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k)` by
      (irule analyzed_computed_operand_demand >> simp[]) >>
    gvs[MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
 `!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
    demand_available fn bb k v` by
   (rpt strip_tac >> irule analyzed_suffix_inventory_demand >>
    simp[] >> qexistsl_tac [`tail`, `n'`, `ps`] >>
    asm_rewrite_tac[] >>
    qpat_x_assum `set tail UNION _ = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
 `ssa_form fn` by gvs[codegen_ready_fn_def] >>
 drule_all definition_support_output_fresh >> strip_tac >>
 `EVERY (\v. ~MEM (Var v) (compute_operands (EL k bb.bb_instructions)) /\
     ~MEM (Var v) tail /\ Var v NOTIN FDOM ps.ps_spilled)
     (EL k bb.bb_instructions).inst_outputs` by
   (gvs[EVERY_MEM, MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
 `MEM (EL k bb.bb_instructions) (fn_insts fn)` by
   (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
 `ALL_DISTINCT (EL k bb.bb_instructions).inst_outputs` by
   metis_tac[codegen_ready_inst_outputs_distinct] >>
 `LENGTH (compute_operands (EL k bb.bb_instructions)) <= 16` by
   (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >> metis_tac[EL_MEM]) >>
 `EVERY (\x. x <> dead_stack_marker) (compute_operands (EL k bb.bb_instructions))` by
   metis_tac[analyzed_compute_operands_no_marker] >>
 suspend "regular"
QED

Resume analyzed_ordinary_inst_bottom_frame[regular]:
 qabbrev_tac `canon = ps with ps_stack := tail` >>
 Cases_on `generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
   (EL k bb.bb_instructions) (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
   F term bb.bb_label canon` >>
 rename1 `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ canon = (cops,cqs)` >>
 `!r. generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
   (EL k bb.bb_instructions) (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
   F term bb.bb_label (canon with ps_stack := REPLICATE r dead_stack_marker ++ canon.ps_stack) =
   (cops,cqs with ps_stack := REPLICATE r dead_stack_marker ++ cqs.ps_stack)` by
   (gen_tac >> irule generate_regular_plan_bottom_frame >>
    simp[Abbr `canon`] >> metis_tac[]) >>
 `canon with ps_stack := REPLICATE n' dead_stack_marker ++ canon.ps_stack = ps` by
   (simp[Abbr `canon`, stackPlanTypesTheory.plan_state_component_equality]) >>
 first_assum (qspec_then `n'` assume_tac) >>
 first_assum (qspec_then `m+n'` assume_tac) >>
 qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
 gvs[Abbr `canon`, GSYM REPLICATE_APPEND, APPEND_ASSOC]
QED

Resume analyzed_ordinary_inst_bottom_frame[offset]:
 `inst_wf (EL k bb.bb_instructions)` by
   (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
 qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def] >> strip_tac >>
 `?x. (EL k bb.bb_instructions).inst_outputs = [x]` by
   (qpat_x_assum `LENGTH _ = 1` mp_tac >> simp[LENGTH_EQ_NUM_compute]) >>
 qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
 drule_all generate_offset_plan_frame >> strip_tac >>
 gvs[APPEND_ASSOC]
QED

Finalise analyzed_ordinary_inst_bottom_frame

Theorem analyzed_suffix_bottom_frame:
 !fn bb dfg cfg base p j ps ops qs m.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 j+p <= LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
   (DROP (j+p) bb.bb_instructions) /\
 (!k. j+p <= k /\ k < LENGTH bb.bb_instructions /\
   (EL k bb.bb_instructions).inst_opcode = JMP ==> SUC k = LENGTH bb.bb_instructions) /\
 (!k targets. j+p <= k /\ k < LENGTH bb.bb_instructions /\
   (EL k bb.bb_instructions).inst_opcode = JMP /\
   join_target_ops (liveness_analyze fn) fn bb.bb_label (EL k bb.bb_instructions) = SOME targets ==>
   ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
   set targets SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k))) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)))) ps /\
 (?n tail. lineage_core n tail ps /\ residual_budget_wf base [] (ps with ps_stack := tail)) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions) ps = SOME (ops,qs)
 ==>
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions)
   (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
 SOME (ops,qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >>
 map_every qid_spec_tac [`ps`,`ops`,`qs`,`j`] >>
 measureInduct_on `LENGTH bb.bb_instructions - (j+p)` >>
 rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
 Cases_on `j+p = LENGTH bb.bb_instructions`
 >- gvs[DROP_LENGTH_TOO_LONG, generate_block_insts_plan_def] >>
 `j+p < LENGTH bb.bb_instructions` by decide_tac >>
 `DROP (j+p) bb.bb_instructions =
    EL (j+p) bb.bb_instructions :: DROP (SUC (j+p)) bb.bb_instructions` by
   simp[DROP_CONS_EL] >>
 `DROP (SUC (j+p)) bb.bb_instructions = [] ==>
    SUC (j+p) = LENGTH bb.bb_instructions` by
   (simp[DROP_EQ_NIL] >> decide_tac) >>
 Cases_on `(EL (j+p) bb.bb_instructions).inst_opcode = JMP`
 >- suspend "jmp" >>
 suspend "ordinary"
QED

Resume analyzed_suffix_bottom_frame[jmp]:
 qpat_x_assum `!y. LENGTH _ - y < _ ==> _` kall_tac >>
 `SUC (j+p) = LENGTH bb.bb_instructions` by
   (first_x_assum irule >> simp[]) >>
 `DROP (SUC (j+p)) bb.bb_instructions = []` by simp[DROP_LENGTH_TOO_LONG] >>
 `MEM (EL (j+p) bb.bb_instructions) bb.bb_instructions` by
   (irule EL_MEM >> decide_tac) >>
 `inst_wf (EL (j+p) bb.bb_instructions)` by
   (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[]) >>
 `compute_operands (EL (j+p) bb.bb_instructions) = [] /\
  (EL (j+p) bb.bb_instructions).inst_outputs = []` by
   gvs[inst_wf_def, compute_operands_def, asmIRTheory.get_non_label_operands_def] >>
 `!targets. join_target_ops (liveness_analyze fn) fn bb.bb_label
      (EL (j+p) bb.bb_instructions) = SOME targets ==>
    ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
    EVERY (\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) targets` by
   (gen_tac >> disch_tac >>
    `ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
     set targets SUBSET set (MAP Var
       (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)))` by
      (qpat_x_assum `!k targets. _` (qspecl_then [`j+p`,`targets`] mp_tac) >> simp[]) >>
    conj_tac >- (first_assum ACCEPT_TAC) >> conj_tac >- (first_assum ACCEPT_TAC) >>
    rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> disch_tac >>
    `MEM op (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)))` by
      (qpat_x_assum `set targets SUBSET _`
        (qspec_then `op` mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
       asm_rewrite_tac[]) >>
    gvs[MEM_MAP] >> drule lineage_inventory_live_membership >>
    strip_tac >> first_x_assum irule >> simp[]) >>
 qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 once_rewrite_tac[generate_block_insts_plan_def] >> asm_rewrite_tac[] >>
 simp[generate_block_insts_plan_def, AllCaseEqs()] >> strip_tac >>
 qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_inst_plan_def, is_param_opcode_def, is_pre_codegen_opcode_def,
      AllCaseEqs()] >> strip_tac >>
 drule_all generate_jmp_plan_bottom_frame >>
 disch_then (qspec_then `m` assume_tac) >>
 asm_rewrite_tac[] >>
 qpat_x_assum `join_reached _ _ _ _ _` mp_tac >> asm_rewrite_tac[] >>
 simp[join_reached_def] >>
 Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label
   (EL (j+p) bb.bb_instructions)` >> simp[] >>
 strip_tac >>
 rename1 `stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack` >>
 `LENGTH targets <= LENGTH qs.ps_stack` by
   (qpat_x_assum `stack_pop _ _ ++ _ = _`
     (mp_tac o AP_TERM ``LENGTH : operand list -> num``) >>
    simp[stackModelTheory.stack_pop_def, LENGTH_TAKE] >> decide_tac) >>
 simp[fnPlanLineagePhiTemporalTheory.stack_pop_bottom_extension, APPEND_ASSOC] >>
 asm_rewrite_tac[]
QED

Resume analyzed_suffix_bottom_frame[ordinary]:
 `EVERY (\inst. inst.inst_opcode <> PHI) (DROP (j+p) bb.bb_instructions)` by
   (gvs[EVERY_MEM] >> metis_tac[]) >>
 `~is_param_opcode (EL (j+p) bb.bb_instructions).inst_opcode` by
   (qpat_x_assum `EVERY (\inst. _ /\ _) _` mp_tac >>
    once_asm_rewrite_tac[] >> simp[]) >>
 qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 once_rewrite_tac[generate_block_insts_plan_def] >> asm_rewrite_tac[] >>
 simp[Once generate_block_insts_plan_def, AllCaseEqs()] >> strip_tac >>
 ` (if LENGTH bb.bb_instructions <= SUC (j+p) then
      live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
    else live_vars_at (liveness_analyze fn) bb.bb_label (j+(p+1))) =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC (j+p))` by
   (IF_CASES_TAC >> simp[] >> AP_TERM_TAC >> decide_tac) >>
 gvs[] >>
 drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
   analyzed_ordinary_inst_bottom_frame >>
 disch_then (qspecl_then [`base'`,`m`] mp_tac) >>
 (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
 `lineage_inventory
    (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (j+p))))) ps' /\
   (?n tail. lineage_core n tail ps' /\
     residual_budget_wf base' [] (ps' with ps_stack := tail))` by
   (Cases_on `(EL (j+p) bb.bb_instructions).inst_opcode = OFFSET`
    >- suspend "offset_step" >>
    qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ (ps with ps_stack := _) = _` kall_tac >>
    drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
      analyzed_ordinary_inst_inventory >>
    disch_then (qspec_then `base'` mp_tac) >>
    (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >>
 qpat_x_assum `!y. LENGTH _ < _ ==> _` (qspec_then `SUC (j+p)` mp_tac) >>
 (impl_tac >- decide_tac) >>
 disch_then (qspecl_then [`j+1`,`p`] mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES] >>
 disch_then (qspecl_then [`qs`,`rest_ops`,`ps'`] mp_tac) >>
 `j+(p+1) = SUC (j+p)` by decide_tac >> asm_rewrite_tac[] >>
 (impl_tac >-
   (simp[] >> conj_tac >-
      (rpt gen_tac >> strip_tac >>
       qpat_x_assum `!k targets. _` (qspecl_then [`k`,`targets`] mp_tac) >>
       (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >> simp[]) >>
    metis_tac[])) >> disch_tac >>
 asm_rewrite_tac[] >> once_rewrite_tac[generate_block_insts_plan_def] >>
 asm_rewrite_tac[] >>
 ` (if LENGTH bb.bb_instructions <= SUC (j+p) then
      live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
    else live_vars_at (liveness_analyze fn) bb.bb_label (SUC (j+p))) =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC (j+p))` by
   (IF_CASES_TAC >> simp[] >> AP_TERM_TAC >> decide_tac) >>
 simp[] >> asm_rewrite_tac[]
QED

Resume analyzed_suffix_bottom_frame[offset_step]:
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ (ps with ps_stack := _) = _` kall_tac >>
  `inst_wf (EL (j+p) bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def] >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
    is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
    venomInstTheory.is_raw_fmp_opcode_def] >> strip_tac >>
  `?x. (EL (j+p) bb.bb_instructions).inst_outputs = [x]` by
    (qpat_x_assum `LENGTH _ = 1` mp_tac >> simp[LENGTH_EQ_NUM_compute]) >>
  irule fnLineageInvOffsetTheory.analyzed_offset_inventory >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Finalise analyzed_suffix_bottom_frame
