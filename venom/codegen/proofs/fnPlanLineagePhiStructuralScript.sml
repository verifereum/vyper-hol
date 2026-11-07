Theory fnPlanLineagePhiStructural
Ancestors
  fnPlanLineageSetup fnPlanLineagePhiResources reorderSim planSpillBounds
  stackModel stackPlanTypes stackPlanGen pred_set rich_list

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
