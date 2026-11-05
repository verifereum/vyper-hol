Theory fnLineageInvBoundary
Ancestors fnPlanPrefix fnPlanLineageInventory list rich_list pred_set stackPlanTypes

Theorem lineage_inventory_live_membership:
  !vs ps. lineage_inventory (set (MAP Var vs)) ps ==>
    (!op. (MEM op ps.ps_stack /\ op <> dead_stack_marker) \/
          op IN FDOM ps.ps_spilled ==> ?v. op = Var v /\ MEM v vs) /\
    (!v. MEM v vs ==> MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule lineage_inventory_stack_subset >>
      drule lineage_inventory_spilled_subset >>
      simp[pred_setTheory.SUBSET_DEF, MEM_MAP] >> metis_tac[]) >>
  gvs[lineage_inventory_def, lineage_core_def,
      pred_setTheory.EXTENSION, MEM_MAP] >>
  metis_tac[MEM_APPEND, pred_setTheory.IN_UNION]
QED

Theorem lineage_inventory_splice_marked_iff:
  !S path dfs base.
    lineage_inventory S path ==>
    (generated_plan_state_wf_marked base
       (dfs with <| ps_stack := path.ps_stack; ps_spilled := path.ps_spilled |>) <=>
     planSpillBounds$plan_slots_bounded base
       (dfs with <| ps_stack := path.ps_stack; ps_spilled := path.ps_spilled |>) /\
     doSwapSim$spill_alloc_layout_wf dfs.ps_alloc path.ps_spilled)
Proof
  rpt gen_tac >>
  simp[lineage_inventory_def, lineage_core_def] >> rpt strip_tac >>
  `~MEM dead_stack_marker core` by
    (gvs[EVERY_MEM] >> strip_tac >>
     first_x_assum drule >>
     simp[stackPlanGenTheory.dead_stack_marker_def,
          stackPlanTypesTheory.is_var_operand_def]) >>
  `dead_stack_marker NOTIN FDOM path.ps_spilled` by
    (strip_tac >> first_x_assum drule >>
     simp[stackPlanGenTheory.dead_stack_marker_def,
          stackPlanTypesTheory.is_var_operand_def]) >>
  `FILTER (\op. op <> dead_stack_marker) (REPLICATE m dead_stack_marker) = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM, MEM_REPLICATE] >>
  `FILTER (\op. op <> dead_stack_marker) core = core` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >> metis_tac[]) >>
  gvs[generated_plan_state_wf_marked_def, FILTER_APPEND,
      DISJOINT_DEF, EXTENSION, MEM_REPLICATE] >> metis_tac[]
QED
