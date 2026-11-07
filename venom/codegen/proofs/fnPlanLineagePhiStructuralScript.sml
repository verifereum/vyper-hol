Theory fnPlanLineagePhiStructural
Ancestors
  fnPlanLineageSetup fnPlanLineagePhiResources fnPlanLineagePhiInventory
  fnPlanLineageInventory
  reorderSim planSpillBounds
  stackModel stackPlanTypes stackPlanGen pred_set list rich_list

Theorem fresh_poke_residual_budget:
  !spillbase ps d y.
    residual_budget_wf spillbase [] ps /\ d < LENGTH ps.ps_stack /\
    ~MEM y ps.ps_stack /\ y NOTIN FDOM ps.ps_spilled ==>
    residual_budget_wf spillbase []
      (ps with ps_stack := stack_poke d y ps.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `plan_slots_bounded spillbase (ps with ps_stack := stack_poke d y ps.ps_stack)` by
    (fs[residual_budget_wf_def, plan_slots_bounded_def] >> simp[plan_slots_bounded_def] >> metis_tac[]) >>
  fs[residual_budget_wf_def, LIST_ELEM_COUNT_THM] >>
  simp[residual_budget_wf_def] >>
  conj_tac
  >- (qx_gen_tac `z` >>
      qpat_assum `!op. LIST_ELEM_COUNT op _ <= 1`
        (qspec_then `z` assume_tac) >>
      drule stack_poke_count_balance >>
      disch_then (qspecl_then [`z`,`y`] mp_tac) >>
      Cases_on `z = y` >>
      Cases_on `z = stack_peek d ps.ps_stack` >>
      gvs[GSYM LIST_ELEM_COUNT_MEM] >>
      strip_tac >>
      qpat_assum `!op. LIST_ELEM_COUNT op _ <= 1`
        (qspec_then `stack_peek d ps.ps_stack` mp_tac) >> decide_tac) >>
  rpt strip_tac >>
  drule stack_poke_count_balance >>
  disch_then (qspecl_then [`op`,`y`] mp_tac) >>
  `op <> y` by metis_tac[] >>
  Cases_on `op = stack_peek d ps.ps_stack` >> gvs[] >>
  res_tac >> decide_tac
QED

Theorem dead_phi_marker_core_resource:
  !ps m core spillbase inst d v next halting ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = Var v /\ ~MEM v next /\
    ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
    Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled /\
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    ?rest. qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      residual_budget_wf spillbase [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule planAlignTheory.stack_find_bound >> simp[]) >>
  `d < LENGTH core` by
    (spose_not_then assume_tac >>
     `LENGTH ps.ps_stack - (d+1) < m` by (gvs[] >> decide_tac) >>
     qpat_x_assum `stack_peek d _ = Var v` mp_tac >>
     pure_asm_rewrite_tac[stack_peek_def] >>
     simp[EL_APPEND1, EL_REPLICATE, dead_stack_marker_def]) >>
  `residual_budget_wf spillbase []
    (ps with ps_stack := stack_poke d (Var (HD inst.inst_outputs)) core)` by
    (drule fresh_poke_residual_budget >>
     disch_then (qspecl_then [`d`,`Var (HD inst.inst_outputs)`] mp_tac) >> gvs[]) >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`,`halting`] mp_tac) >>
  simp[fnPlanLineagePhiTemporalTheory.phi_write_phase_def, operand_to_string_def] >>
  strip_tac >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `popmany_plan [ret] written = _` >>
      `ps2 = SND (popmany_plan [ret] written)` by gvs[] >>
      drule_at (Pat `qs = SND _`) popmany_plan_core_resource >>
      disch_then (qspecl_then [`REPLICATE m dead_stack_marker`,
        `stack_poke d ret core`,`spillbase`] mp_tac) >>
      (impl_tac
       >- (simp[Abbr `written`,
                fnPlanLineageInventoryTheory.stack_poke_bottom_extension] >>
           simp[Abbr `ret`, DISJOINT_DEF, EXTENSION, dead_stack_marker_def])) >>
      metis_tac[]) >>
  qexists_tac `stack_poke d (Var (HD inst.inst_outputs)) core` >>
  simp[fnPlanLineageInventoryTheory.stack_poke_bottom_extension]
QED

Theorem dup_fresh_output_core_resource:
  !ps m core spillbase d y ops dup.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    d < LENGTH ps.ps_stack /\
    ~MEM (Var y) ps.ps_stack /\ Var y NOTIN FDOM ps.ps_spilled /\
    stackPlanOps$do_dup d ps = (ops,dup) ==>
    residual_budget_wf spillbase [] (dup with ps_stack := core ++ [Var y]) /\
    stack_poke 0 (Var y) dup.ps_stack = ps.ps_stack ++ [Var y]
Proof
  rpt gen_tac >> strip_tac >>
  `plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (gvs[residual_budget_wf_def, plan_slots_bounded_def] >> metis_tac[]) >>
  drule_all planSpillBoundsTheory.do_dup_slots_bounded >> strip_tac >>
  drule doSwapSimTheory.do_dup_stack_exact >> strip_tac >>
  drule_all doSwapSimTheory.do_dup_layout_wf >> strip_tac >> gvs[] >>
  `residual_budget_wf spillbase [] (ps with ps_stack := core ++ [Var y])` by
    (qspec_then `[y]` mp_tac fresh_outputs_residual_budget >>
     disch_then (qspecl_then [`ps with ps_stack := core`,`spillbase`] mp_tac) >>
     gvs[]) >>
  conj_tac
  >- (gvs[residual_budget_wf_def, plan_slots_bounded_def] >> metis_tac[]) >>
  simp[stack_poke_def, LUPDATE_APPEND2, LUPDATE_def]
QED

Theorem live_phi_marker_core_resource:
  !ps m core spillbase inst d v next halting ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = Var v /\ MEM v next /\
    ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
    Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled /\
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    ?rest. qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      residual_budget_wf spillbase [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule planAlignTheory.stack_find_bound >> simp[]) >>
  Cases_on `stackPlanOps$do_dup d ps` >> rename1 `stackPlanOps$do_dup d ps = (dups,dup)` >>
  `residual_budget_wf spillbase []
      (dup with ps_stack := core ++ [Var (HD inst.inst_outputs)]) /\
   stack_poke 0 (Var (HD inst.inst_outputs)) dup.ps_stack =
      ps.ps_stack ++ [Var (HD inst.inst_outputs)]` by
    (irule dup_fresh_output_core_resource >>
     simp[] >> conj_tac >- (qexists_tac `m` >> simp[]) >>
     qexistsl_tac [`d`,`dups`] >> gvs[]) >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`,`halting`] mp_tac) >>
  simp[fnPlanLineagePhiTemporalTheory.phi_write_phase_def, operand_to_string_def] >>
  strip_tac >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `popmany_plan [ret] written = _` >>
      `ps2 = SND (popmany_plan [ret] written)` by gvs[] >>
      drule_at (Pat `qs = SND _`) popmany_plan_core_resource >>
      disch_then (qspecl_then [`REPLICATE m dead_stack_marker`,
        `core ++ [ret]`,`spillbase`] mp_tac) >>
      (impl_tac
       >- (simp[Abbr `written`] >>
           simp[Abbr `ret`, DISJOINT_DEF, EXTENSION, dead_stack_marker_def])) >>
      metis_tac[]) >>
  qexists_tac `core ++ [Var (HD inst.inst_outputs)]` >> simp[]
QED

Theorem selected_phi_marker_core_resource:
  !S ps m core base inst d v next halting ops qs.
    lineage_inventory S ps /\ lineage_core m core ps /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = Var v /\
    Var (HD inst.inst_outputs) NOTIN S /\
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    ?rest. lineage_core m rest qs /\
      residual_budget_wf base [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (Var (HD inst.inst_outputs)) ps.ps_stack` by
    (drule lineage_inventory_stack_subset >>
     simp[SUBSET_DEF, dead_stack_marker_def] >>
     disch_then (qspec_then `Var (HD inst.inst_outputs)` mp_tac) >> simp[]) >>
  `Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled` by
    (drule lineage_inventory_spilled_subset >> simp[SUBSET_DEF] >> metis_tac[]) >>
  Cases_on `MEM v next`
  >- (drule_all (REWRITE_RULE [GSYM lineage_core_def] live_phi_marker_core_resource) >>
      simp[]) >>
  drule_all (REWRITE_RULE [GSYM lineage_core_def] dead_phi_marker_core_resource) >> simp[]
QED

Theorem selected_phi_next_demand_coverage:
  !S ps inst d v next halting ops qs.
    lineage_inventory S ps /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = Var v /\
    Var (HD inst.inst_outputs) NOTIN S /\
    generate_phi_plan inst next halting ps = (ops,qs) /\
    set (MAP Var next) SUBSET S UNION {Var (HD inst.inst_outputs)} ==>
    set (MAP Var next) SUBSET set qs.ps_stack UNION FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all generate_phi_plan_lineage_inventory >> strip_tac >>
  rename1 `lineage_inventory inventory ps` >>
  `set (MAP Var next) SUBSET
    (((if MEM v next then inventory else inventory DELETE (Var v)) UNION
      {Var (HD inst.inst_outputs)}) DIFF
      (if ~halting /\ ~MEM (HD inst.inst_outputs) next
       then {Var (HD inst.inst_outputs)} else {}))` by
    (gvs[SUBSET_DEF, MEM_MAP] >> rpt strip_tac >>
     qpat_x_assum `!x. _ ==> x IN inventory \/ _`
       (qspec_then `Var y` mp_tac) >> simp[] >>
     Cases_on `MEM v next` >>
     Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >>
     gvs[] >> metis_tac[]) >>
  fs[lineage_inventory_def, lineage_core_def] >>
  ASM_SET_TAC[]
QED
