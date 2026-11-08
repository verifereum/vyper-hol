Theory fnPlanLineageWide
Ancestors fnPlanLineageInventory
Libs stackPlanOpsTheory stackModelTheory fnPlanLineageReorderTheory listTheory

(* Materialisation shields arbitrary residual prefixes even for wide joins.
   The preservation lemmas here do not assume a short target window. *)
Theorem reorder_one_wide_counts:
  !dfg targets idx op ps ops qs d.
    idx < LENGTH targets /\ LENGTH targets <= LENGTH ps.ps_stack /\
    MEM op targets /\
    stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
      (LENGTH targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    !x. MEM x targets ==>
      LIST_ELEM_COUNT x qs.ps_stack = LIST_ELEM_COUNT x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets - 1 - idx = LENGTH targets - (idx + 1)` by decide_tac >>
  gvs[] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> rename1 `_ = (reduce_ops,mid)` >>
  `LENGTH targets <= LENGTH mid.ps_stack` by
    (Cases_on `d > 16` >> gvs[] >>
     drule reduce_depth_plan_target_length_floor >>
     simp[arithmeticTheory.MIN_DEF, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!x. MEM x targets ==>
    LIST_ELEM_COUNT x mid.ps_stack = LIST_ELEM_COUNT x ps.ps_stack` by
    (Cases_on `d > 16` >> gvs[] >>
     metis_tac[reorderSimTheory.reduce_depth_plan_pending_stack_count_unconditional]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) mid.ps_stack`
  >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  `dist < LENGTH mid.ps_stack /\ stack_peek dist mid.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH targets - (idx + 1) < LENGTH mid.ps_stack` by decide_tac >>
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  qspecl_then [`dfg`, `op`, `dist`, `LENGTH targets - (idx + 1)`, `mid`, `x`]
    mp_tac reorderSimTheory.reorder_place_phase_multiplicity >> simp[] >>
  Cases_on `dist = LENGTH targets - (idx + 1)` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist mid.ps_stack)
    (stack_peek (LENGTH targets - (idx + 1)) mid.ps_stack)` >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem do_swap_wide_peek_other:
  !d k ps. d < LENGTH ps.ps_stack /\ k < LENGTH ps.ps_stack /\
    k <> 0 /\ k <> d ==>
    stack_peek k (SND (do_swap d ps)).ps_stack = stack_peek k ps.ps_stack
Proof
  rpt strip_tac >> simp[doSwapSimTheory.do_swap_stack_result] >>
  Cases_on `d = 0` >>
  simp[stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE] >>
  `LENGTH ps.ps_stack - 1 - k <> PRE (LENGTH ps.ps_stack)` by decide_tac >>
  `LENGTH ps.ps_stack - 1 - k <> LENGTH ps.ps_stack - (d + 1)` by decide_tac >>
  simp[]
QED

Theorem do_swap_wide_peek_ends:
  !d ps. d < LENGTH ps.ps_stack ==>
    stack_peek d (SND (do_swap d ps)).ps_stack = stack_peek 0 ps.ps_stack /\
    stack_peek 0 (SND (do_swap d ps)).ps_stack = stack_peek d ps.ps_stack
Proof
  rpt strip_tac >> simp[doSwapSimTheory.do_swap_stack_result,
    stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE]
QED

Theorem reorder_place_wide_fixed:
  !dfg op dist final_dist k ps.
    dist < LENGTH ps.ps_stack /\ final_dist < LENGTH ps.ps_stack /\
    k < LENGTH ps.ps_stack /\ k <> 0 /\ k <> dist /\ k <> final_dist ==>
    stack_peek k
      (if dist = final_dist then ps
       else if operand_equiv dfg op (stack_peek final_dist ps.ps_stack) then
         ps with ps_stack := stack_poke final_dist op
           (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)
       else SND (do_swap final_dist (SND (do_swap dist ps)))).ps_stack =
    stack_peek k ps.ps_stack
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `dist = final_dist` >> simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek final_dist ps.ps_stack)` >> simp[]
  >- simp[stack_peek_def, stack_poke_def, EL_LUPDATE] >>
  Cases_on `do_swap dist ps` >> gvs[] >>
  rename1 `do_swap dist ps = (s1,ps1)` >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by
    (qspecl_then [`dist`, `ps`] mp_tac planWfTheory.do_swap_length >> simp[]) >>
  Cases_on `do_swap final_dist ps1` >> gvs[] >>
  `stack_peek k ps1.ps_stack = stack_peek k ps.ps_stack` by
    metis_tac[do_swap_wide_peek_other, pairTheory.SND] >>
  metis_tac[do_swap_wide_peek_other, pairTheory.SND]
QED

Theorem reorder_place_wide_places:
  !dfg op dist final_dist ps.
    dist < LENGTH ps.ps_stack /\ final_dist < LENGTH ps.ps_stack /\
    stack_peek dist ps.ps_stack = op ==>
    stack_peek final_dist
      (if dist = final_dist then ps
       else if operand_equiv dfg op (stack_peek final_dist ps.ps_stack) then
         ps with ps_stack := stack_poke final_dist op
           (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)
       else SND (do_swap final_dist (SND (do_swap dist ps)))).ps_stack = op
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `dist = final_dist` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist ps.ps_stack)
    (stack_peek final_dist ps.ps_stack)` >> simp[]
  >- simp[stack_peek_def, stack_poke_def, EL_LUPDATE] >>
  Cases_on `do_swap dist ps` >> gvs[] >>
  rename1 `do_swap dist ps = (s1,ps1)` >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by
    (qspecl_then [`dist`, `ps`] mp_tac planWfTheory.do_swap_length >> simp[]) >>
  Cases_on `do_swap final_dist ps1` >> gvs[] >>
  `stack_peek 0 ps1.ps_stack = stack_peek dist ps.ps_stack` by
    metis_tac[do_swap_wide_peek_ends, pairTheory.SND] >>
  metis_tac[do_swap_wide_peek_ends, pairTheory.SND]
QED

Theorem reorder_one_wide_preserves_fixed:
  !dfg targets idx op ps ops qs i d.
    idx < LENGTH targets /\ i < idx /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
      (LENGTH targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    stack_peek (LENGTH targets - 1 - i) qs.ps_stack =
    stack_peek (LENGTH targets - 1 - i) ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets - 1 - idx = LENGTH targets - (idx + 1)` by decide_tac >>
  `LENGTH targets - 1 - i = LENGTH targets - (i + 1)` by decide_tac >>
  `reduce_depth_plan (LENGTH ps.ps_stack) targets op
      (LENGTH targets - (idx + 1)) (LENGTH targets) ps = ([],ps)` by
    (Cases_on `LENGTH ps.ps_stack` >> simp[reduce_depth_plan_def] >> decide_tac) >>
  `d < LENGTH ps.ps_stack /\
    ~(LENGTH targets - (idx + 1) < d /\ d < LENGTH targets)` by
    metis_tac[stack_get_unfixed_depth_props] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  Cases_on `d > 16` >> simp[] >>
  qspecl_then [`dfg`, `op`, `d`, `LENGTH targets - (idx + 1)`,
    `LENGTH targets - (i + 1)`, `ps`] mp_tac reorder_place_wide_fixed >>
  (impl_tac >- decide_tac) >>
  Cases_on `d = LENGTH targets - (idx + 1)` >> gvs[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH targets - (idx + 1)) ps.ps_stack)` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Theorem reorder_one_wide_places:
  !dfg targets idx op ps ops qs d.
    idx < LENGTH targets /\ LENGTH targets <= LENGTH ps.ps_stack /\
    MEM op targets /\
    stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
      (LENGTH targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    stack_peek (LENGTH targets - 1 - idx) qs.ps_stack = op
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets - 1 - idx = LENGTH targets - (idx + 1)` by decide_tac >>
  gvs[] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> rename1 `_ = (reduce_ops,mid)` >>
  `LENGTH targets <= LENGTH mid.ps_stack` by
    (Cases_on `d > 16` >> gvs[] >>
     drule reduce_depth_plan_target_length_floor >>
     simp[arithmeticTheory.MIN_DEF, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `?dist. stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) mid.ps_stack = SOME dist` by
    (Cases_on `d > 16` >> gvs[] >>
     drule_all planWfTheory.reduce_depth_plan_dist_ge >>
     disch_then (qspec_then `LENGTH ps.ps_stack` mp_tac) >>
     simp[LET_THM] >> metis_tac[]) >>
  `dist < LENGTH mid.ps_stack /\ stack_peek dist mid.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH targets - (idx + 1) < LENGTH mid.ps_stack` by decide_tac >>
  simp[] >> strip_tac >>
  qspecl_then [`dfg`, `op`, `dist`, `LENGTH targets - (idx + 1)`, `mid`]
    mp_tac reorder_place_wide_places >> simp[] >>
  Cases_on `dist = LENGTH targets - (idx + 1)` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist mid.ps_stack)
    (stack_peek (LENGTH targets - (idx + 1)) mid.ps_stack)` >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem reorder_one_wide_step:
  !dfg targets idx ps ops qs.
    idx < LENGTH targets /\ LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < idx ==>
      stack_peek (LENGTH targets - 1 - i) ps.ps_stack = EL i targets) /\
    reorder_one dfg targets idx (EL idx targets) ps = (ops,qs) ==>
    LENGTH targets <= LENGTH qs.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x qs.ps_stack = LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < SUC idx ==>
      stack_peek (LENGTH targets - 1 - i) qs.ps_stack = EL i targets)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> Cases_on `MEM x targets`
     >- simp[] >> gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >>
  `?d. stack_get_unfixed_depth (EL idx targets)
      (LENGTH targets - 1 - idx) (LENGTH targets) ps.ps_stack = SOME d` by
    metis_tac[reorderSimTheory.materialised_pending_next_on_stack_window] >>
  `MEM (EL idx targets) targets` by simp[EL_MEM] >>
  conj_tac >- metis_tac[reorder_one_target_length] >>
  conj_tac >- metis_tac[reorder_one_wide_counts] >>
  gen_tac >> strip_tac >> Cases_on `i = idx`
  >- (qpat_x_assum `i = idx` SUBST_ALL_TAC >>
      metis_tac[reorder_one_wide_places]) >>
  `i < idx` by decide_tac >>
  metis_tac[reorder_one_wide_preserves_fixed]
QED
