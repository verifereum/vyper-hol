Theory fnAliasInvPhi
Ancestors
  fnFrameStepsPhi fnPlanPrefix stackPlanGen
  fnBlockPlanStaticRegion fnLineageStatic

(* The value boundary depends on planner provenance, not assembly execution. *)
Theorem phi_provenance_final_alias:
  !base fn bb pred entry source final ra lo last dfg.
  phi_run_context fn bb pred entry source final /\
  phi_stack_provenance base pred entry
    (collect_phis bb.bb_instructions) [] last /\
  generated_plan_state_wf_marked base entry /\
  dfg = dfg_build_function fn /\
  (!op v. (MEM op entry.ps_stack \/ op IN FDOM entry.ps_spilled) /\
    ~(MEM op entry.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
      resolve_phi pred inst.inst_operands = SOME op) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
  (!at. MEM at entry.ps_stack \/ at IN FDOM entry.ps_spilled ==>
    operand_val (frame_view fn ra source) lo at =
    operand_val (frame_view fn ra source) lo (normalize_operand dfg [] at)) ==>
  !at. MEM at last.ps_stack \/ at IN FDOM last.ps_spilled ==>
    operand_val (frame_view fn ra final) lo at =
    operand_val (frame_view fn ra final) lo (normalize_operand dfg [] at)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  drule_all phi_provenance_final_resident >> disch_then DISJ_CASES_TAC
  >- (irule phi_eval_preserves_frame_alias >>
      qexistsl_tac [`collect_phis bb.bb_instructions`, `source`] >>
      gvs[phi_run_context_def] >>
      rpt strip_tac >>
      `~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
        (qpat_x_assum `!op v. _` irule >> qexists_tac `at` >> simp[]) >>
      gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      metis_tac[livenessProofsTheory.collect_phis_mem]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  `ssa_form fn` by gvs[phi_run_context_def, codegen_ready_fn_def] >>
  `MEM inst (fn_insts fn)` by
    (gvs[phi_run_context_def] >>
     metis_tac[allocaRemapSSATheory.mem_fn_insts_intro,
       livenessProofsTheory.collect_phis_mem]) >>
  `inst.inst_opcode = PHI` by
    metis_tac[phi_codegen_inst_shape, phi_run_context_def] >>
  metis_tac[phi_output_normalize_self]
QED

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
