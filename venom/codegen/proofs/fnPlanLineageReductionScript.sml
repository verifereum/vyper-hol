Theory fnPlanLineageReduction
Ancestors
  planWf stackModel stackPlanOps

Theorem reduce_depth_step_height:
  !targets op f n ps dist cand ops ps'.
    stack_get_unfixed_depth op f n ps.ps_stack = SOME dist /\
    16 < dist /\
    select_spill_candidate ps.ps_stack targets dist n = SOME cand /\
    do_spill_at cand ps = (ops, ps') ==>
    0 < LENGTH ps.ps_stack /\
    LENGTH ps'.ps_stack + 1 = LENGTH ps.ps_stack
Proof
  rpt strip_tac >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule do_spill_at_length_exact >>
  disch_then (qspec_then `cand` mp_tac) >> simp[]
QED

Theorem reduce_depth_plan_adequate_fuel:
  !ps k m targets op f n.
    LENGTH ps.ps_stack <= k /\ LENGTH ps.ps_stack <= m ==>
    reduce_depth_plan k targets op f n ps =
    reduce_depth_plan m targets op f n ps
Proof
  measureInduct_on `LENGTH ps.ps_stack` >>
  rpt strip_tac >>
  Cases_on `k`
  >- (Cases_on `m` >> gvs[reduce_depth_plan_def,
        stack_get_unfixed_depth_def, stack_get_depth_def, stack_find_def]) >>
  Cases_on `m`
  >- (gvs[reduce_depth_plan_def,
        stack_get_unfixed_depth_def, stack_get_depth_def, stack_find_def]) >>
  simp[Ntimes reduce_depth_plan_def 2] >>
  Cases_on `f + 1 < n` >- simp[] >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack`
  >- simp[] >>
  rename1 `stack_get_unfixed_depth op f n ps.ps_stack = SOME dist` >>
  Cases_on `dist <= 16` >- simp[] >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist n`
  >- simp[] >>
  rename1 `select_spill_candidate ps.ps_stack targets dist n = SOME cand` >>
  Cases_on `do_spill_at cand ps` >>
  rename1 `do_spill_at cand ps = (spill_ops, ps')` >>
  `16 < dist` by decide_tac >>
  `0 < LENGTH ps.ps_stack /\
   LENGTH ps'.ps_stack + 1 = LENGTH ps.ps_stack` by
    (drule_all reduce_depth_step_height >> simp[]) >>
  `reduce_depth_plan n' targets op f n ps' =
   reduce_depth_plan n'' targets op f n ps'` by
    (first_x_assum (qspec_then `ps'.ps_stack` mp_tac) >>
     simp[] >> disch_then irule >> decide_tac) >>
  simp[]
QED

Theorem reduce_depth_plan_height_fuel:
  !ps k targets op f n.
    LENGTH ps.ps_stack <= k ==>
    reduce_depth_plan (LENGTH ps.ps_stack) targets op f n ps =
    reduce_depth_plan k targets op f n ps
Proof
  rpt strip_tac >> irule reduce_depth_plan_adequate_fuel >> simp[]
QED
