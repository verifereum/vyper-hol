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

Theorem stack_poke_top_exchange:
  !stk d.
    d < LENGTH stk ==>
    stack_poke 0 (stack_peek d stk)
      (stack_poke d (stack_peek 0 stk) stk) = stack_swap d stk
Proof
  rpt strip_tac >>
  simp[stack_poke_def, stack_peek_def, stack_swap_def] >>
  irule LIST_EQ >> simp[EL_LUPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem do_swap_lineage_inventory:
  !inventory_set ps d.
    lineage_inventory inventory_set ps /\ d < LENGTH ps.ps_stack /\
    is_var_operand (stack_peek d ps.ps_stack) ==>
    lineage_inventory inventory_set (SND (do_swap d ps))
Proof
  rpt gen_tac >> simp[lineage_inventory_def, lineage_core_def] >>
  rpt strip_tac >>
  `d < LENGTH core` by
    (spose_not_then assume_tac >>
     gvs[stack_peek_def, EL_APPEND_EQN, EL_REPLICATE,
       dead_stack_marker_def, is_var_operand_def]) >>
  drule_all do_swap_core >> strip_tac >>
  qexistsl [`m`, `stack_swap d core`] >>
  simp[reorderSimTheory.do_swap_spilled_unchanged] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem singleton_poke_lineage_inventory:
  !inventory_set ps a d.
    lineage_inventory inventory_set ps /\
    stack_get_unfixed_depth (Var a) 0 1 ps.ps_stack = SOME d ==>
    lineage_inventory inventory_set
      (ps with ps_stack := stack_poke 0 (Var a)
        (stack_poke d (stack_peek 0 ps.ps_stack) ps.ps_stack))
Proof
  rpt strip_tac >> drule stack_get_unfixed_depth_props >> strip_tac >>
  `is_var_operand (stack_peek d ps.ps_stack)` by simp[is_var_operand_def] >>
  drule_all do_swap_lineage_inventory >>
  `stack_poke 0 (Var a) (stack_poke d (stack_peek 0 ps.ps_stack) ps.ps_stack) =
    stack_swap d ps.ps_stack` by metis_tac[stack_poke_top_exchange] >>
  simp[lineage_inventory_def, lineage_core_def,
    doSwapSimTheory.do_swap_stack_result, reorderSimTheory.do_swap_spilled_unchanged]
QED

Theorem reorder_singleton_lineage_inventory:
  !inventory_set dfg a ps.
    lineage_inventory inventory_set ps ==>
    lineage_inventory inventory_set (SND (reorder_plan dfg [Var a] ps))
Proof
  rpt strip_tac >>
  simp[reorder_plan_def, indexedListsTheory.MAPi_def, reorder_one_def] >>
  pairarg_tac >> simp[] >>
  qpat_x_assum `_ = (step_ops,ps')` mp_tac >>
  pairarg_tac >> simp[] >>
  `lineage_inventory inventory_set ps1` by
    (qpat_x_assum `_ = (restore_ops,ps1)` mp_tac >>
     Cases_on `stack_get_unfixed_depth (Var a) 0 1 ps.ps_stack` >> simp[]
     >- (Cases_on `FLOOKUP ps.ps_spilled (Var a)` >> simp[] >>
         strip_tac >> gvs[] >>
         metis_tac[do_restore_lineage_inventory, pairTheory.SND]) >>
     strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth (Var a) 0 1 ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `lineage_inventory inventory_set ps2` by
    (qpat_x_assum `_ = (reduce_ops,ps2)` mp_tac >>
     Cases_on `x > 16` >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[reduce_depth_plan_lineage_inventory, pairTheory.SND]) >>
  Cases_on `stack_get_unfixed_depth (Var a) 0 1 ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME placed` >>
  Cases_on `placed = 0` >> simp[]
  >- (strip_tac >> gvs[]) >>
  `placed < LENGTH ps2.ps_stack /\ stack_peek placed ps2.ps_stack = Var a` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `0 < LENGTH ps2.ps_stack` by decide_tac >> simp[] >>
  Cases_on `operand_equiv dfg (Var a) (stack_peek 0 ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[] >> irule singleton_poke_lineage_inventory >> metis_tac[]) >>
  simp[Q.SPEC `0` do_swap_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `is_var_operand (stack_peek placed ps2.ps_stack)` by simp[is_var_operand_def] >>
  drule_all do_swap_lineage_inventory >> simp[]
QED

(* Placement, separately from exact inventory conservation. *)
Theorem reorder_singleton_source_top:
  !dfg a ps.
    IS_SOME (stack_get_unfixed_depth (Var a) 0 1 ps.ps_stack) ==>
    stack_peek 0 (SND (reorder_plan dfg [Var a] ps)).ps_stack = Var a
Proof
  rpt strip_tac >>
  Cases_on `stack_get_unfixed_depth (Var a) 0 1 ps.ps_stack` >> gvs[] >>
  simp[reorder_plan_def, indexedListsTheory.MAPi_def, reorder_one_def] >>
  pairarg_tac >> simp[] >>
  qpat_x_assum `_ = (step_ops,ps')` mp_tac >>
  pairarg_tac >> simp[] >>
  `IS_SOME (stack_get_unfixed_depth (Var a) 0 1 ps2.ps_stack)` by
    (qpat_x_assum `_ = (_,ps2)` mp_tac >>
     Cases_on `x > 16` >> simp[] >> strip_tac >> gvs[] >>
     drule_at (Pat `reduce_depth_plan _ _ _ _ _ _ = _`)
       reduce_depth_plan_unfixed_hit >> simp[]) >>
  Cases_on `stack_get_unfixed_depth (Var a) 0 1 ps2.ps_stack` >> gvs[] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME d` >>
  `d < LENGTH ps2.ps_stack /\ stack_peek d ps2.ps_stack = Var a` by
    metis_tac[stack_get_unfixed_depth_props] >>
  Cases_on `d = 0` >- (strip_tac >> gvs[]) >>
  `0 < LENGTH ps2.ps_stack` by decide_tac >> simp[] >>
  Cases_on `operand_equiv dfg (Var a) (stack_peek 0 ps2.ps_stack)`
  >- (strip_tac >> gvs[] >>
      simp[stack_poke_def, stack_peek_def, EL_LUPDATE]) >>
  simp[Q.SPEC `0` do_swap_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  `ps'.ps_stack = stack_swap d ps2.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >>
  gvs[stack_swap_def, stack_peek_def, EL_LUPDATE]
QED
