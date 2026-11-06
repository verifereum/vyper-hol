(*
 * Planner steps that keep generated_plan_state_wf_marked (fnPlanPrefix):
 * do_swap, pops, popmany_plan, and clean_stack_plan's marking and
 * forgetting of dead stack slots.  Planner-level only, so the lineage
 * theories below the frame proofs can use them too.
 *)

Theory planWfMarked
Ancestors
  deepResidualBudget reorderSim fnPlanPrefix planSpillBounds doSwapSim stackModel stackPlanOps
  stackPlanGen stackPlanTypes sorting list rich_list pred_set pair combin

Theorem do_swap_wf_marked:
  !base ps dist ops ps'.
    generated_plan_state_wf_marked base ps /\
    dist < LENGTH ps.ps_stack /\
    do_swap dist ps = (ops, ps') ==>
    generated_plan_state_wf_marked base ps'
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generated_plan_state_wf_marked bound ps` >>
  `plan_slots_bounded bound ps'` by
    metis_tac[planSpillBoundsTheory.do_swap_plan_slots_bounded,
              generated_plan_state_wf_marked_def] >>
  `sorting$PERM ps'.ps_stack ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_perm, pairTheory.SND] >>
  `ps'.ps_spilled = ps.ps_spilled /\
   doSwapSim$spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled` by
    metis_tac[doSwapSimTheory.do_swap_layout_wf,
              generated_plan_state_wf_marked_def, pairTheory.SND] >>
  gvs[generated_plan_state_wf_marked_def] >> conj_tac
  >- metis_tac[sortingTheory.PERM_FILTER, sortingTheory.ALL_DISTINCT_PERM] >>
  fs[pred_setTheory.IN_DISJOINT] >> metis_tac[sortingTheory.PERM_MEM_EQ]
QED

Theorem wf_marked_stack_sublist:
  !base ps stk.
    generated_plan_state_wf_marked base ps /\
    (!op. MEM op stk ==> MEM op ps.ps_stack) /\
    ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) stk) ==>
    generated_plan_state_wf_marked base (ps with ps_stack := stk)
Proof
  simp[generated_plan_state_wf_marked_def, pred_setTheory.IN_DISJOINT] >>
  metis_tac[]
QED

Theorem wf_marked_pop:
  !base ps n.
    generated_plan_state_wf_marked base ps ==>
    generated_plan_state_wf_marked base
      (ps with ps_stack := stack_pop n ps.ps_stack)
Proof
  rpt strip_tac >> irule wf_marked_stack_sublist >>
  simp[stackModelTheory.stack_pop_def] >>
  conj_tac >- metis_tac[rich_listTheory.MEM_TAKE] >>
  qpat_x_assum `generated_plan_state_wf_marked _ _` mp_tac >>
  simp[generated_plan_state_wf_marked_def] >> strip_tac >>
  `ps.ps_stack = TAKE (LENGTH ps.ps_stack - n) ps.ps_stack ++
                 DROP (LENGTH ps.ps_stack - n) ps.ps_stack` by
    simp[] >>
  metis_tac[listTheory.FILTER_APPEND_DISTRIB, listTheory.ALL_DISTINCT_APPEND]
QED

Theorem popmany_individual_wf_marked:
  !xs base ps ops ps'.
    generated_plan_state_wf_marked base ps /\
    popmany_individual xs ps = (ops, ps') ==>
    generated_plan_state_wf_marked base ps'
Proof
  simp[stackPlanOpsTheory.popmany_individual_def] >> rpt gen_tac >>
  rename1 `generated_plan_state_wf_marked bound _` >>
  qmatch_goalsub_abbrev_tac `FOLDL popf acc0 sorted` >>
  `!items acc.
     generated_plan_state_wf_marked bound (SND acc) ==>
     generated_plan_state_wf_marked bound (SND (FOLDL popf acc items))` by
    (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     first_x_assum irule >> PairCases_on `acc` >> gvs[] >>
     simp[Abbr `popf`] >>
     Cases_on `stack_get_depth h acc1.ps_stack` >> simp[] >>
     rename1 `stack_get_depth h acc1.ps_stack = SOME dist` >>
     drule stackModelTheory.stack_get_depth_props >> strip_tac >>
     Cases_on `dist = 0` >> simp[]
     >- metis_tac[wf_marked_pop, pairTheory.SND] >>
     pairarg_tac >> simp[] >>
     metis_tac[wf_marked_pop, do_swap_wf_marked, pairTheory.SND]) >>
  rpt strip_tac >> first_x_assum (qspec_then `sorted` mp_tac) >>
  disch_then (qspec_then `acc0` mp_tac) >>
  gvs[Abbr `acc0`]
QED

Theorem popmany_plan_wf_marked:
  !xs base ps ops ps'.
    generated_plan_state_wf_marked base ps /\
    popmany_plan xs ps = (ops, ps') ==>
    generated_plan_state_wf_marked base ps'
Proof
  Cases >- simp[stackPlanOpsTheory.popmany_plan_def] >>
  simp[stackPlanOpsTheory.popmany_plan_def] >> rpt gen_tac >>
  reverse IF_CASES_TAC
  >- metis_tac[popmany_individual_wf_marked] >>
  reverse IF_CASES_TAC
  >- metis_tac[popmany_individual_wf_marked] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `is_contiguous_top depths` >>
  `!v. IS_SOME (stack_get_depth v ps.ps_stack) ==>
       THE (stack_get_depth v ps.ps_stack) < LENGTH ps.ps_stack` by
    (gen_tac >> Cases_on `stack_get_depth v ps.ps_stack` >> simp[] >>
     metis_tac[stackModelTheory.stack_get_depth_props]) >>
  `!d. MEM d depths ==> d < LENGTH ps.ps_stack` by
    (simp[Abbr `depths`, listTheory.MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `MEM (SUC (LENGTH t)) depths` by
    (`LENGTH depths = SUC (LENGTH t)` by simp[Abbr `depths`] >>
     `MEM (SUC (LENGTH t)) (QSORT (\a b. a <= b) depths)` by
       gvs[stackPlanOpsTheory.is_contiguous_top_def, listTheory.MEM_GENLIST] >>
     metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]) >>
  `SUC (LENGTH t) < LENGTH ps.ps_stack` by metis_tac[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[do_swap_wf_marked, wf_marked_pop]
QED

Theorem mark_dead_stack_filter:
  !retained stk.
    FILTER (\op. op <> dead_stack_marker) (mark_dead_stack retained stk) =
    FILTER (\op. ~MEM op retained)
      (FILTER (\op. op <> dead_stack_marker) stk)
Proof
  gen_tac >> Induct >> gvs[mark_dead_stack_def] >>
  gen_tac >> Cases_on `MEM h retained` >>
  Cases_on `h = dead_stack_marker` >> gvs[]
QED

Theorem mark_dead_stack_mem:
  !retained stk op.
    MEM op (mark_dead_stack retained stk) ==>
    op = dead_stack_marker \/ MEM op stk
Proof
  simp[mark_dead_stack_def, MEM_MAP] >> metis_tac[]
QED

Theorem mark_dead_stack_wf_marked:
  !base ps retained.
    generated_plan_state_wf_marked base ps ==>
    generated_plan_state_wf_marked base
      (ps with ps_stack := mark_dead_stack retained ps.ps_stack)
Proof
  simp[generated_plan_state_wf_marked_def, mark_dead_stack_filter] >>
  rpt strip_tac
  >- metis_tac[FILTER_ALL_DISTINCT] >>
  fs[IN_DISJOINT] >> metis_tac[mark_dead_stack_mem]
QED

Theorem forget_stack_wf_marked:
  !base ps.
    generated_plan_state_wf_marked base ps ==>
    generated_plan_state_wf_marked base
      (ps with ps_stack := MAP (K dead_stack_marker) ps.ps_stack)
Proof
  rpt gen_tac >>
  `FILTER (K F) ps.ps_stack = []` by simp[FILTER_EQ_NIL] >>
  simp[generated_plan_state_wf_marked_def, FILTER_MAP,
       IN_DISJOINT, MEM_MAP, combinTheory.K_THM] >>
  metis_tac[]
QED

Theorem clean_stack_plan_wf_marked:
  !base ps liveness cfg fn bb ops ps'.
    generated_plan_state_wf_marked base ps /\
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
    generated_plan_state_wf_marked base ps'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
  Cases_on `t` >> simp[]
  >- (IF_CASES_TAC
      >- (simp[] >> rpt strip_tac >> gvs[]) >>
      Cases_on `lookup_block h fn.fn_blocks`
      >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
      qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      IF_CASES_TAC
      >- (strip_tac >> gvs[] >>
          drule forget_stack_wf_marked >>
          simp[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
          metis_tac[]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> strip_tac >> gvs[] >>
          `generated_plan_state_wf_marked base' ps''` by
            metis_tac[popmany_plan_wf_marked] >>
          drule mark_dead_stack_wf_marked >>
          simp[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
          metis_tac[]) >>
      metis_tac[popmany_plan_wf_marked]) >>
  strip_tac >> gvs[]
QED

Theorem phi_popmany_fold_spilled[local]:
  !xs acc ps.
    (SND (FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
        let (swap_ops, ps') =
          if dist = 0 then ([] : stack_op list, ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack)) (acc, ps) xs)).ps_spilled =
    ps.ps_spilled
Proof
  Induct_on `xs` >- simp[] >> rpt gen_tac >>
  gvs[LET_THM] >> simp[Once listTheory.FOLDL] >>
  Cases_on `stack_get_depth h ps.ps_stack` >- simp[] >> simp[] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  Cases_on `dist = 0` >> simp[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[reorderSimTheory.do_swap_spilled_unchanged, pairTheory.SND]
QED

Theorem phi_do_swap_spilled_result[local]:
  !dist ps ops ps'. do_swap dist ps = (ops, ps') ==> ps'.ps_spilled = ps.ps_spilled
Proof
  rpt strip_tac >>
  qspecl_then [`dist`, `ps`] mp_tac reorderSimTheory.do_swap_spilled_unchanged >>
  simp[]
QED

Theorem phi_popmany_fold_spilled_result[local]:
  !xs acc ps ops ps'.
    FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
        let (swap_ops, ps') =
          if dist = 0 then ([] : stack_op list, ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack)) (acc, ps) xs = (ops, ps') ==>
    ps'.ps_spilled = ps.ps_spilled
Proof
  rpt strip_tac >>
  qspecl_then [`xs`, `acc`, `ps`] mp_tac phi_popmany_fold_spilled >> simp[]
QED

Theorem phi_popmany_spilled:
  !xs ps ops ps'. popmany_plan xs ps = (ops, ps') ==> ps'.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> Cases_on `xs` >> simp[stackPlanOpsTheory.popmany_plan_def,
       stackPlanOpsTheory.popmany_individual_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[SRULE [LET_THM] phi_popmany_fold_spilled_result,
            phi_do_swap_spilled_result]
QED

Theorem phi_plan_spilled_unchanged:
  !inst live halt ps ops ps'.
    generate_phi_plan inst live halt ps = (ops, ps') ==>
    ps'.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[generate_phi_plan_def, LET_THM] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- simp[] >>
  simp[] >> rpt (IF_CASES_TAC >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) live` >> gvs[] >>
  imp_res_tac phi_popmany_spilled >> imp_res_tac deepResidualBudgetTheory.do_dup_spilled_eq >> gvs[]
QED
