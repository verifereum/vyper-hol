Theory fnLineageInvReorderMultiplicity
Ancestors
  fnPlanLineageReorder reorderSim stackPlanOps stackModel finite_map planWf list rich_list

Theorem reduce_depth_plan_pending_inventory_count:
  !fuel pending target_op f ps ops qs x.
    MEM x pending /\
    reduce_depth_plan fuel pending target_op f (LENGTH pending) ps =
      (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target_op f (LENGTH pending)
              ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < LENGTH pending` >> gvs[] >>
  Cases_on `x' <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x'
              (LENGTH pending)` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    (drule_all select_spill_candidate_bound >> simp[]) >>
  `~MEM (stack_peek cand ps.ps_stack) pending` by
    metis_tac[select_spill_candidate_var_not_pending] >>
  `LIST_ELEM_COUNT x ps1.ps_stack = LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[do_spill_at_other_stack_count] >>
  `?off. ps1.ps_spilled =
    ps.ps_spilled |+ (stack_peek cand ps.ps_stack,off)` by
    metis_tac[do_spill_at_spilled_update] >>
  `x IN FDOM ps1.ps_spilled <=> x IN FDOM ps.ps_spilled` by
    (simp[FDOM_FUPDATE] >> metis_tac[]) >>
  Cases_on `reduce_depth_plan fuel pending target_op f
              (LENGTH pending) ps1` >> gvs[] >>
  first_x_assum (drule_then (drule_then mp_tac)) >>
  simp[FDOM_FUPDATE]
QED

(* The unguarded final placement in reorder_one also calls do_swap when
   the target distance lies beyond the materialised stack. *)
Theorem do_swap_outside_stack_projection:
  !d ps.
    16 < d /\ LENGTH ps.ps_stack <= d ==>
    (SND (do_swap d ps)).ps_stack =
      EL d ps.ps_stack ::
        (MAP (\i. EL (i + 1) ps.ps_stack) (GENLIST I (d - 1)) ++
         [EL 0 ps.ps_stack])
Proof
  rpt strip_tac >> simp[do_swap_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[top_n_def, TAKE_LENGTH_TOO_LONG, MAP_APPEND, MAP_GENLIST] >>
  `LENGTH ps.ps_stack - (d + 1) = 0` by decide_tac >>
  simp[combinTheory.o_DEF]
QED
