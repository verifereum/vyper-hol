Theory fnLineageInvCleanupCoherence
Ancestors fnPlanLineageInventory stackPlanGen stackPlanTypes stackModel
  list rich_list pred_set

Theorem clean_stack_plan_decision_coherence:
  !m n core P Q lv cfg fn bb opsP P' opsQ Q'.
    lineage_core m core P /\ lineage_core n core Q /\
    ALL_DISTINCT core /\ EVERY is_var_operand core /\
    P.ps_alloc = Q.ps_alloc /\ P.ps_spilled = Q.ps_spilled /\
    (!p pb inputs layout physical retained removed.
      cfg_preds_of cfg bb.bb_label = [p] /\
      1 < LENGTH (cfg_succs_of cfg p) /\
      lookup_block p fn.fn_blocks = SOME pb /\
      inputs = input_vars_from p bb.bb_instructions (live_vars_at lv bb.bb_label 0) /\
      layout = live_vars_at lv p (LENGTH pb.bb_instructions) /\
      physical = FILTER (\op. IS_SOME (stack_get_depth op P.ps_stack))
        (MAP Var (FILTER (\v. ~MEM v inputs) layout)) /\
      retained = FILTER (\op. below_all_live op inputs P.ps_stack) physical /\
      removed = FILTER (\op. ~MEM op retained) physical ==>
      (P.ps_cleanup_promised \/ cleanup_elision_safe P.ps_cleanup_height
        P.ps_cleanup_growth cfg fn bb (LENGTH P.ps_stack - LENGTH removed)) =
      (Q.ps_cleanup_promised \/ cleanup_elision_safe Q.ps_cleanup_height
        Q.ps_cleanup_growth cfg fn bb (LENGTH Q.ps_stack - LENGTH removed))) /\
    (!p pb. cfg_preds_of cfg bb.bb_label = [p] /\
      1 < LENGTH (cfg_succs_of cfg p) /\
      lookup_block p fn.fn_blocks = SOME pb ==>
      set core SUBSET
        set (MAP Var (input_vars_from p bb.bb_instructions
          (live_vars_at lv bb.bb_label 0))) UNION
        set (MAP Var (live_vars_at lv p (LENGTH pb.bb_instructions)))) /\
    clean_stack_plan lv cfg fn bb P = (opsP,P') /\
    clean_stack_plan lv cfg fn bb Q = (opsQ,Q') ==>
    opsP = opsQ /\ P'.ps_alloc = Q'.ps_alloc /\
    P'.ps_spilled = P.ps_spilled /\ Q'.ps_spilled = Q.ps_spilled /\
    ?m' n' core'. lineage_core m' core' P' /\ lineage_core n' core' Q' /\
      ALL_DISTINCT core' /\ EVERY is_var_operand core'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?p pb. cfg_preds_of cfg bb.bb_label = [p] /\
    1 < LENGTH (cfg_succs_of cfg p) /\ lookup_block p fn.fn_blocks = SOME pb`
  >- (pop_assum strip_assume_tac >> suspend "active") >>
  `!s. clean_stack_plan lv cfg fn bb s = ([],s)` by
    (gen_tac >> Cases_on `cfg_preds_of cfg bb.bb_label` >>
     simp[clean_stack_plan_def] >>
     Cases_on `t` >> simp[clean_stack_plan_def] >>
     Cases_on `LENGTH (cfg_succs_of cfg h) <= 1` >> simp[] >>
     Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
     metis_tac[arithmeticTheory.NOT_LESS_EQUAL]) >>
  gvs[] >> qexistsl_tac [`m`, `n`, `core`] >> simp[]
QED

Resume clean_stack_plan_decision_coherence[active]:
  qabbrev_tac `inputs = input_vars_from p bb.bb_instructions (live_vars_at lv bb.bb_label 0)` >>
  qabbrev_tac `layout = live_vars_at lv p (LENGTH pb.bb_instructions)` >>
  qabbrev_tac `to_pop = FILTER (\v. ~MEM v inputs) layout` >>
  qabbrev_tac `physical = FILTER (\op. IS_SOME (stack_get_depth op P.ps_stack)) (MAP Var to_pop)` >>
  qabbrev_tac `retained = FILTER (\op. below_all_live op inputs P.ps_stack) physical` >>
  qabbrev_tac `removed = FILTER (\op. ~MEM op retained) physical` >>
  `~MEM dead_stack_marker core` by
    (fs[EVERY_MEM] >> strip_tac >> first_x_assum drule >>
     simp[is_var_operand_def, dead_stack_marker_def]) >>
  `bottom_dead_equiv P.ps_stack Q.ps_stack` by
    (simp[bottom_dead_equiv_def] >> qexistsl_tac [`m`, `n`, `core`] >>
     gvs[lineage_core_def]) >>
  `~MEM dead_stack_marker (MAP Var to_pop)` by simp[MEM_MAP, dead_stack_marker_def] >>
  `physical = FILTER (\op. IS_SOME (stack_get_depth op Q.ps_stack)) (MAP Var to_pop)` by
    (simp[Abbr `physical`] >> irule bottom_dead_equiv_physical >> simp[]) >>
  `retained = FILTER (\op. below_all_live op inputs Q.ps_stack) physical` by
    (drule_all bottom_dead_equiv_cleanup_partitions >>
     disch_then (qspec_then `inputs` mp_tac) >>
     simp[Abbr `retained`, Abbr `physical`]) >>
  `set physical = set (MAP Var to_pop) INTER set core` by
    (simp[Abbr `physical`, EXTENSION, MEM_FILTER, stack_get_depth_is_some] >>
     qpat_x_assum `lineage_core m core P` mp_tac >>
     qpat_x_assum `~MEM dead_stack_marker (MAP Var to_pop)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[lineage_core_def] >>
     rpt strip_tac >> simp[MEM_REPLICATE] >> metis_tac[]) >>
  `set (MAP Var to_pop) = set (MAP Var layout) DIFF set (MAP Var inputs)` by
    (simp[Abbr `to_pop`, EXTENSION, MEM_MAP, MEM_FILTER] >> Cases >> simp[] >> metis_tac[]) >>
  `set core SUBSET set (MAP Var inputs) UNION set (MAP Var layout)` by
    (simp[Abbr `inputs`, Abbr `layout`] >> metis_tac[]) >>
  `set physical = set core DIFF set (MAP Var inputs)` by ASM_SET_TAC[] >>
  qabbrev_tac `ok = (P.ps_cleanup_promised \/
    cleanup_elision_safe P.ps_cleanup_height P.ps_cleanup_growth cfg fn bb
      (LENGTH P.ps_stack - LENGTH removed))` >>
  `ok = (Q.ps_cleanup_promised \/
    cleanup_elision_safe Q.ps_cleanup_height Q.ps_cleanup_growth cfg fn bb
      (LENGTH Q.ps_stack - LENGTH removed))` by
    (simp[Abbr `ok`] >> first_x_assum irule >>
     rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `inputs`, Abbr `layout`, Abbr `physical`, Abbr `to_pop`,
          Abbr `retained`, Abbr `removed`]) >>
  qabbrev_tac `prefP = (P.ps_cleanup_promised \/ (ok /\ ~NULL retained))` >>
  qabbrev_tac `prefQ = (Q.ps_cleanup_promised \/ (ok /\ ~NULL retained))` >>
  `clean_stack_plan lv cfg fn bb P =
    if NULL inputs /\ ok then
      ([], P with <|ps_stack := MAP (K dead_stack_marker) P.ps_stack;
                    ps_cleanup_promised := prefP|>)
    else if ok then (FST (popmany_plan removed P),
      (SND (popmany_plan removed P)) with
        <|ps_stack := mark_dead_stack retained (SND (popmany_plan removed P)).ps_stack;
          ps_cleanup_promised := prefP|>)
    else popmany_plan (MAP Var to_pop) P` by
    (irule clean_stack_plan_active_payload >> rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `inputs`, Abbr `layout`, Abbr `to_pop`, Abbr `physical`,
          Abbr `retained`, Abbr `removed`, Abbr `ok`, Abbr `prefP`]) >>
  `clean_stack_plan lv cfg fn bb Q =
    if NULL inputs /\ ok then
      ([], Q with <|ps_stack := MAP (K dead_stack_marker) Q.ps_stack;
                    ps_cleanup_promised := prefQ|>)
    else if ok then (FST (popmany_plan removed Q),
      (SND (popmany_plan removed Q)) with
        <|ps_stack := mark_dead_stack retained (SND (popmany_plan removed Q)).ps_stack;
          ps_cleanup_promised := prefQ|>)
    else popmany_plan (MAP Var to_pop) Q` by
    (irule clean_stack_plan_active_payload >> rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `inputs`, Abbr `layout`, Abbr `to_pop`, Abbr `removed`, Abbr `prefQ`]) >>
  Cases_on `ok`
  >- (Cases_on `NULL inputs` >- suspend "empty" >> suspend "retained") >>
  suspend "popped"
QED

Resume clean_stack_plan_decision_coherence[empty]:
  gvs[] >> qexistsl_tac [`LENGTH P.ps_stack`, `LENGTH Q.ps_stack`, `[]`] >>
  simp[lineage_core_def, LIST_EQ_REWRITE, EL_MAP, EL_REPLICATE, combinTheory.K_DEF]
QED

Resume clean_stack_plan_decision_coherence[retained]:
  `retained = FILTER (\op. below_all_live op inputs P.ps_stack) physical` by
    simp[Abbr `retained`] >>
  `removed = FILTER (\op. ~MEM op retained) physical` by simp[Abbr `removed`] >>
  drule_all cleanup_retained_prefix_replay >> strip_tac >>
  rpt (qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `popmany_plan _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `mark_dead_stack _ _ = _` mp_tac) >>
  qpat_x_assum `ALL_DISTINCT live` mp_tac >>
  qpat_x_assum `EVERY is_var_operand live` mp_tac >>
  qpat_x_assum `~NULL inputs` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`m + LENGTH pre`, `n + LENGTH pre`, `live`] >>
  simp[lineage_core_def]
QED

Resume clean_stack_plan_decision_coherence[popped]:
  `?ops live al.
    popmany_plan (MAP Var to_pop) P =
      (ops, P with <|ps_stack := REPLICATE m dead_stack_marker ++ live; ps_alloc := al|>) /\
    popmany_plan (MAP Var to_pop) Q =
      (ops, Q with <|ps_stack := REPLICATE n dead_stack_marker ++ live; ps_alloc := al|>) /\
    ALL_DISTINCT live /\ set live = set core DIFF set (MAP Var to_pop)` by
    (irule popmany_plan_prefix_frame >>
     simp[DISJOINT_ALT, MEM_REPLICATE, MEM_MAP, dead_stack_marker_def] >>
     fs[lineage_core_def, dead_stack_marker_def]) >>
  `EVERY is_var_operand live` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `MEM e core` by ASM_SET_TAC[] >> metis_tac[]) >>
  rpt (qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `popmany_plan _ _ = _` mp_tac) >>
  qpat_x_assum `ALL_DISTINCT live` mp_tac >>
  qpat_x_assum `EVERY is_var_operand live` mp_tac >>
  qpat_x_assum `P.ps_spilled = Q.ps_spilled` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`m`, `n`, `live`] >> simp[lineage_core_def]
QED

Finalise clean_stack_plan_decision_coherence
