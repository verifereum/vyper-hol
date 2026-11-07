Theory fnPlanLineagePhysicalOps
Ancestors fnPlanLineageInventory stackPlanOps stackPlanTypes stackModel stackPlanGen
  planWf list rich_list pred_set finite_map

Theorem distinct_stack_peek_lookup:
  !core prefix op d.
    ALL_DISTINCT core /\ d < LENGTH core /\ stack_peek d core = op ==>
    stack_get_depth op (prefix ++ core) = SOME d
Proof
  rpt strip_tac >>
  `MEM op core` by
    (gvs[stack_peek_def] >> irule EL_MEM >> decide_tac) >>
  drule stack_get_depth_core >>
  disch_then (qspec_then `prefix` strip_assume_tac) >>
  `d' = d` by
    (gvs[stack_peek_def] >>
     `LENGTH core - (d' + 1) < LENGTH core /\
      LENGTH core - (d + 1) < LENGTH core` by decide_tac >>
     `LENGTH core - (d' + 1) = LENGTH core - (d + 1)` by
       metis_tac[ALL_DISTINCT_EL_IMP] >> decide_tac) >>
  gvs[]
QED

Theorem lineage_inventory_variable_peek_lookup:
  !S ps v d.
    lineage_inventory S ps /\ d < LENGTH ps.ps_stack /\
    stack_peek d ps.ps_stack = Var v ==>
    stack_get_depth (Var v) ps.ps_stack = SOME d
Proof
  rpt gen_tac >> simp[lineage_inventory_def, lineage_core_def] >>
  rpt strip_tac >>
  `d < LENGTH core` by
    (spose_not_then assume_tac >>
     gvs[stack_peek_def, EL_APPEND_EQN, EL_REPLICATE,
       dead_stack_marker_def]) >>
  `stack_peek d core = Var v` by
    gvs[stack_peek_def, EL_APPEND_EQN] >>
  asm_rewrite_tac[] >> irule distinct_stack_peek_lookup >> simp[]
QED

Theorem select_spill_candidate_inventory_lookup:
  !S ps forbidden dist target_len cand.
    lineage_inventory S ps /\ 1 <= LENGTH ps.ps_stack /\
    select_spill_candidate ps.ps_stack forbidden dist target_len = SOME cand ==>
    ?v. stack_get_depth (Var v) ps.ps_stack = SOME cand /\ cand <= 16
Proof
  rpt strip_tac >>
  drule select_spill_candidate_props >> strip_tac >>
  `?v. stack_peek cand ps.ps_stack = Var v` by
    (Cases_on `stack_peek cand ps.ps_stack` >>
     gvs[is_var_operand_def]) >>
  drule_all select_spill_candidate_bound >> strip_tac >>
  qexists `v` >> simp[] >>
  irule lineage_inventory_variable_peek_lookup >> metis_tac[]
QED

Theorem reduce_depth_plan_lineage_inventory:
  !fuel target_ops target_op f target_len S ps.
    lineage_inventory S ps ==>
    lineage_inventory S
      (SND (reduce_depth_plan fuel target_ops target_op f target_len ps))
Proof
  Induct >> simp[reduce_depth_plan_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `lineage_inventory inventory_set ps` >>
  Cases_on `f + 1 < target_len` >> simp[] >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >> simp[] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops dist target_len` >> simp[] >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  drule_all select_spill_candidate_inventory_lookup >> strip_tac >>
  `lineage_inventory inventory_set (SND (do_spill_at cand ps))` by
    (irule do_spill_at_lineage_inventory >> metis_tac[]) >>
  Cases_on `do_spill_at cand ps` >> gvs[] >>
  first_x_assum drule >>
  disch_then (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`] mp_tac) >>
  Cases_on `reduce_depth_plan fuel target_ops target_op f target_len r` >>
  gvs[]
QED
