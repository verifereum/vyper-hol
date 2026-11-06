Theory fnLineageInvTerminal
Ancestors
  fnPlanLineageReorder fnPlanLineageInventory stackPlanOps stackModel
  reorderSim planWf

Theorem full_support_select_spill_candidate_none:
  !stk targets dist n.
    stk <> [] /\
    (!op. MEM op stk /\ is_var_operand op ==> MEM op targets) ==>
    select_spill_candidate stk targets dist n = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `select_spill_candidate stk targets dist n` >> simp[] >>
  rename1 `select_spill_candidate stk targets dist n = SOME cand` >>
  drule select_spill_candidate_var_not_pending >> strip_tac >>
  `1 <= LENGTH stk` by (Cases_on `stk` >> gvs[]) >>
  drule_all planWfTheory.select_spill_candidate_bound >> strip_tac >>
  drule reorderSimTheory.stack_peek_mem >> strip_tac >>
  metis_tac[]
QED

Theorem full_support_reduce_depth_plan_identity:
  !fuel targets target f n ps.
    (!op. MEM op ps.ps_stack /\ is_var_operand op ==> MEM op targets) ==>
    reduce_depth_plan fuel targets target f n ps = ([],ps)
Proof
  Cases >> rpt gen_tac >> strip_tac >>
  simp[Once reduce_depth_plan_def] >>
  Cases_on `ps.ps_stack = []`
  >- simp[stack_get_unfixed_depth_def, stack_get_depth_def, stack_find_def] >>
  drule_all full_support_select_spill_candidate_none >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target f n' ps.ps_stack` >> simp[]
QED
