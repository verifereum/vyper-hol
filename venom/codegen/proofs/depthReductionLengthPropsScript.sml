(* Stack height consumed by a bounded depth reduction. *)
Theory depthReductionLengthProps
Ancestors
  stackPlanOps stackPlanTypes stackModel list rich_list arithmetic finite_map

Theorem do_spill_at_length_exact:
  !cand ps. 1 <= LENGTH ps.ps_stack ==>
    LENGTH (SND (do_spill_at cand ps)).ps_stack = LENGTH ps.ps_stack - 1
Proof
  rpt strip_tac >> simp[do_spill_at_def] >>
  Cases_on `cand = 0`
  >- (simp[do_spill_tos_def, LET_THM] >>
      Cases_on `alloc_spill_slot ps.ps_alloc` >> simp[stack_pop_def])
  >> simp[LET_THM] >>
  Cases_on `do_spill_tos (ps with ps_stack := stack_swap cand ps.ps_stack)` >>
  simp[] >>
  fs[do_spill_tos_def, LET_THM] >>
  Cases_on `alloc_spill_slot
    (ps with ps_stack := stack_swap cand ps.ps_stack).ps_alloc` >>
  gvs[stack_pop_def, stack_swap_def, LENGTH_LUPDATE]
QED

Theorem reduce_depth_plan_excess_length_floor:
  !fuel targets op f width ps ops post.
    reduce_depth_plan fuel targets op f width ps = (ops,post) ==>
    LENGTH ps.ps_stack - fuel <= LENGTH post.ps_stack
Proof
  Induct >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  Cases_on `f + 1 < width` >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f width ps.ps_stack` >> simp[] >>
  rename1 `_ = SOME dist` >>
  Cases_on `dist <= 16` >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist width` >> simp[] >>
  rename1 `_ = SOME cand` >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,mid)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `LENGTH mid.ps_stack = LENGTH ps.ps_stack - 1` by
    (qspecl_then [`cand`, `ps`] mp_tac do_spill_at_length_exact >> simp[]) >>
  first_x_assum drule >> simp[] >> decide_tac
QED
