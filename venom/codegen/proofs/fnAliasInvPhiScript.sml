Theory fnAliasInvPhi
Ancestors
  fnFrameStepsPhi fnPlanPrefix stackPlanGen
  fnBlockPlanStaticRegion fnLineageStatic fnBlockPlanStaticBodyPrefix

Theorem phi_provenance_prefix:
  !base fn bb pred entry source final dfg cfg halt i j ps ops qs.
    phi_run_context fn bb pred entry source final /\
    i+j <= LENGTH (collect_phis bb.bb_instructions) /\
    phi_stack_provenance base pred entry
      (TAKE i (collect_phis bb.bb_instructions))
      (DROP i (collect_phis bb.bb_instructions)) ps /\
    generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
      halt 0 (LENGTH bb.bb_instructions) i j (DROP i bb.bb_instructions) ps =
      SOME (ops,qs) ==>
    phi_stack_provenance base pred entry
      (TAKE (i+j) (collect_phis bb.bb_instructions))
      (DROP (i+j) (collect_phis bb.bb_instructions)) qs
Proof
  Induct_on `j`
  >- simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` livenessProofsTheory.current_collect_phis_length) >>
     decide_tac) >>
  `DROP i bb.bb_instructions = EL i bb.bb_instructions :: DROP (i+1) bb.bb_instructions` by
    metis_tac[rich_listTheory.DROP_CONS_EL, arithmeticTheory.ADD1] >>
  `(EL i bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[fnBlockPlanStaticOffsetLiveTheory.collect_phis_index] >>
  `LENGTH bb.bb_instructions = SUC i + LENGTH (DROP (i+1) bb.bb_instructions)` by
    simp[listTheory.LENGTH_DROP] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [phi_prefix_cons_plan] >>
  Cases_on `generate_phi_plan (EL i bb.bb_instructions)
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halt ps` >>
  simp_tac bool_ss [LET_THM, pairTheory.pair_case_thm, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `LENGTH bb.bb_instructions = _` (fn th =>
    rule_assum_tac (REWRITE_RULE [GSYM th])) >>
  gvs[AllCaseEqs()] >>
  rename1 `generate_phi_plan _ _ _ ps = (step_ops, mid)` >>
  `i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `EL i (collect_phis bb.bb_instructions) = EL i bb.bb_instructions` by
    simp[fnBlockPlanStaticOffsetLiveTheory.collect_phis_index] >>
  `DROP i (collect_phis bb.bb_instructions) =
    EL i bb.bb_instructions :: DROP (SUC i) (collect_phis bb.bb_instructions)` by
    (drule rich_listTheory.DROP_CONS_EL >> simp[]) >>
  `TAKE (SUC i) (collect_phis bb.bb_instructions) =
    TAKE i (collect_phis bb.bb_instructions) ++ [EL i bb.bb_instructions]` by
    metis_tac[rich_listTheory.TAKE_SUC_BY_TAKE, listTheory.SNOC_APPEND,
      fnBlockPlanStaticOffsetLiveTheory.collect_phis_index] >>
  `phi_stack_provenance base' pred entry
    (TAKE (SUC i) (collect_phis bb.bb_instructions))
    (DROP (SUC i) (collect_phis bb.bb_instructions)) mid` by
    (asm_simp_tac bool_ss [] >>
     irule phi_provenance_advance >>
     qexistsl_tac [`bb`, `fn`] >>
     simp[listTheory.LENGTH_TAKE] >>
     goal_assum (drule_at Any) >>
     gvs[phi_run_context_def] >>
     metis_tac[listTheory.TAKE_DROP]) >>
  `i + SUC j = SUC i + j` by decide_tac >>
  pop_assum SUBST1_TAC >> first_x_assum irule >>
  metis_tac[arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES]
QED

Theorem lineage_entry_selected_phi_start:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) pred lbl ps /\
  collect_phis bb.bb_instructions <> [] ==>
  regional_selected_phi_inv (liveness_analyze fn) (dfg_build_function fn) sb bb 0 ps
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `~(LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1)` by
    metis_tac[ready_small_preds_no_phis] >>
  `ps.ps_spilled = FEMPTY` by
    (irule phi_join_entry_spill_empty >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fnLineageStaticTheory.lineage_entry_phi_sources >>
  simp[listTheory.EVERY_MEM] >> strip_tac >>
  simp[fnBlockPlanStaticRegionTheory.regional_selected_phi_inv_def] >>
  conj_tac >- metis_tac[fnLineageStaticTheory.lineage_entry_marked] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >>
    simp[EXISTS_UNIQUE_THM] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    drule_all fnLineageStaticTheory.lineage_entry_coverage >> simp[]) >>
  metis_tac[fnLineageStaticTheory.lineage_entry_non_phi_fresh]
QED

Theorem lineage_entry_actual_phi_source:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  bb <> HD fn.fn_blocks /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) edge lbl ps /\
  (!x. MEM x (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0)) ==>
    MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
  MEM phi (collect_phis bb.bb_instructions) /\
  resolve_phi pred phi.inst_operands = SOME (Var src) ==>
  MEM (Var src) ps.ps_stack /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
      venomExecPropsTheory.lookup_block_label] >>
  drule_all phi_codegen_inst_shape >> strip_tac >>
  `MEM (pred,src) (phi_pairs phi.inst_operands)` by
    (gvs[cfgNormBaseTheory.resolve_phi_phi_pairs] >>
     metis_tac[alistTheory.ALOOKUP_MEM]) >>
  `MEM src (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))` by
    metis_tac[phi_selected_input_vars] >>
  `MEM (Var src) ps.ps_stack \/ Var src IN FDOM ps.ps_spilled` by metis_tac[] >>
  `MEM (Var src) phi.inst_operands` by
    metis_tac[cfgNormBaseTheory.phi_pairs_mem_var] >>
  `collect_phis bb.bb_instructions <> []` by metis_tac[listTheory.MEM] >>
  drule_all lineage_entry_selected_phi_start >>
  simp[regional_selected_phi_inv_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED

Theorem lineage_phi_prefix_lower_inv:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) pred lbl ps /\
  collect_phis bb.bb_instructions <> [] /\
  generate_block_insts_prefix (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label halt 0 (LENGTH bb.bb_instructions) 0
    (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
    SOME (ops,qs) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb
    (LENGTH (collect_phis bb.bb_instructions)) qs
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  drule_all fnLineageStaticTheory.lineage_entry_edge >> strip_tac >>
  drule_all lineage_entry_selected_phi_start >> strip_tac >>
  irule regional_selected_phi_exit_lower_inv >>
  `regional_selected_phi_inv (liveness_analyze fn) (dfg_build_function fn) sb bb 0
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)` by
    simp[regional_selected_phi_inv_cleanup_fields] >>
  irule (GEN_ALL (SRULE []
    (Q.INST [`i` |-> `0`] (SPEC_ALL
      (INST_TYPE [``:'a`` |-> ``:cfg_analysis``] regional_selected_phi_inv_prefix))))) >>
  simp[] >>
  qexistsl_tac [`cfg_analyze fn`, `halt`, `ops`,
    `ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>`] >>
  gvs[]
QED

Theorem lineage_phi_context_unselected_fresh:
  codegen_ready_fn fn /\
  (!inst op. MEM inst (collect_phis bb.bb_instructions) /\
    is_var_operand op /\ MEM op inst.inst_operands /\ MEM op ps.ps_stack ==>
    resolve_phi pred inst.inst_operands = SOME op) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) edge lbl ps /\
  collect_phis bb.bb_instructions <> [] ==>
  !op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    ~(MEM op ps.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
      resolve_phi pred inst.inst_operands = SOME op) /\
    (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `~(LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1)` by
    metis_tac[ready_small_preds_no_phis] >>
  `ps.ps_spilled = FEMPTY` by
    (irule phi_join_entry_spill_empty >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  rpt gen_tac >> strip_tac >>
  `?w. op = Var w` by
    (Cases_on `op` >> gvs[dfgDefsTheory.normalize_operand_def]) >>
  `~MEM op (FLAT (MAP (\inst. inst.inst_operands)
    (collect_phis bb.bb_instructions)))` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP, phi_run_context_def] >>
     metis_tac[stackPlanTypesTheory.is_var_operand_def]) >>
  metis_tac[fnLineageStaticTheory.lineage_entry_non_phi_fresh]
QED

Theorem lineage_phi_prefix_alias:
  phi_run_context fn bb pred
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) source final /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) edge lbl ps /\
  collect_phis bb.bb_instructions <> [] /\
  generate_block_insts_prefix (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label halt 0 (LENGTH bb.bb_instructions) 0
    (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
    SOME (ops,qs) /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra source) lo at =
    operand_val (frame_view fn ra source) lo
      (normalize_operand (dfg_build_function fn) [] at)) ==>
  !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
    operand_val (frame_view fn ra final) lo at =
    operand_val (frame_view fn ra final) lo
      (normalize_operand (dfg_build_function fn) [] at)
Proof
  strip_tac >>
  `codegen_ready_fn fn` by gvs[phi_run_context_def] >>
  `generated_plan_state_wf_marked sb ps` by
    metis_tac[fnLineageStaticTheory.lineage_entry_marked] >>
  `generated_plan_state_wf_marked sb
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)` by
    simp[wf_marked_cleanup_fields] >>
  `phi_run_context fn bb pred ps source final` by
    (gvs[phi_run_context_def] >> metis_tac[]) >>
  `!inst op. MEM inst (collect_phis bb.bb_instructions) /\
    is_var_operand op /\ MEM op inst.inst_operands /\ MEM op ps.ps_stack ==>
    resolve_phi pred inst.inst_operands = SOME op` by
    gvs[phi_run_context_def] >>
  drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)
    lineage_phi_context_unselected_fresh >>
  disch_then (qspec_then `pred` mp_tac) >> simp[] >> strip_tac >>
  `phi_stack_provenance sb pred
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
    (collect_phis bb.bb_instructions) [] qs` by
    (irule (GEN_ALL (SRULE [] (Q.INST [`i` |-> `0`,
      `j` |-> `LENGTH (collect_phis bb.bb_instructions)`]
      (SPEC_ALL (INST_TYPE [``:'a`` |-> ``:cfg_analysis``] phi_provenance_prefix))))) >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[phi_stack_provenance_init]) >>
  rpt gen_tac >> disch_tac >>
  irule phi_provenance_final_alias >>
  simp[] >>
  goal_assum (drule_at (Pat `phi_stack_provenance _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `phi_run_context _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem lineage_phi_eval_context:
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) edge lbl ps /\
  collect_phis bb.bb_instructions <> [] /\ source.vs_prev_bb = SOME pred /\
  (!x. MEM x (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0)) ==>
    MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
  eval_phis source bb.bb_instructions = OK final ==>
  phi_run_context fn bb pred
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) source final
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `eval_phis source (collect_phis bb.bb_instructions) = OK final` by
    simp[phi_eval_collect] >>
  `!inst op. MEM inst (collect_phis bb.bb_instructions) /\
    is_var_operand op /\ MEM op inst.inst_operands /\ MEM op ps.ps_stack ==>
    resolve_phi pred inst.inst_operands = SOME op` by
    (rpt gen_tac >> strip_tac >>
     `EVERY (\i. i.inst_opcode = PHI) (collect_phis bb.bb_instructions)` by
       (simp[listTheory.EVERY_MEM] >> metis_tac[phi_codegen_inst_shape]) >>
     drule_all phi_eval_member_result >> strip_tac >>
     `phi_well_formed inst.inst_operands` by metis_tac[phi_codegen_inst_shape] >>
     `?src. resolve_phi pred inst.inst_operands = SOME (Var src)` by
       (gvs[venomExecSemanticsTheory.eval_one_phi_def, AllCaseEqs()] >>
        metis_tac[venomWfPropsTheory.resolve_phi_well_formed]) >>
     drule_all lineage_entry_actual_phi_source >> strip_tac >>
     Cases_on `op` >> gvs[stackPlanTypesTheory.is_var_operand_def] >> metis_tac[]) >>
  drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)
    lineage_phi_context_unselected_fresh >>
  disch_then (qspec_then `pred` mp_tac) >> simp[] >> strip_tac >>
  `!inst out. MEM inst (collect_phis bb.bb_instructions) /\ MEM out inst.inst_outputs ==>
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled` by
    (rpt gen_tac >> disch_tac >> irule phi_entry_outputs_absent >>
     qexistsl_tac [`bb`, `dfg_build_function fn`, `fn`] >>
     qexistsl_tac [`inst`, `pred`] >> simp[] >> metis_tac[]) >>
  simp[phi_run_context_def] >> metis_tac[]
QED

Theorem lineage_phi_eval_exit:
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) edge lbl ps /\
  collect_phis bb.bb_instructions <> [] /\ source.vs_prev_bb = SOME pred /\
  (!x. MEM x (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0)) ==>
    MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
  eval_phis source bb.bb_instructions = OK final /\
  generate_block_insts_prefix (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label halt 0 (LENGTH bb.bb_instructions) 0
    (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
    SOME (ops,qs) /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra source) lo at =
    operand_val (frame_view fn ra source) lo
      (normalize_operand (dfg_build_function fn) [] at)) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb
    (LENGTH (collect_phis bb.bb_instructions)) qs /\
  (!at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
    operand_val (frame_view fn ra final) lo at =
    operand_val (frame_view fn ra final) lo
      (normalize_operand (dfg_build_function fn) [] at))
Proof
  strip_tac >>
  conj_tac >- (irule lineage_phi_prefix_lower_inv >> metis_tac[]) >>
  `phi_run_context fn bb pred
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) source final` by
    (irule lineage_phi_eval_context >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  irule lineage_phi_prefix_alias >>
  goal_assum (drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED
