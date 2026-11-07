Theory fnPlanLineageAssignRegion
Ancestors fnPlanLineageCanonicalAssign fnPlanLineageSetup venomInst stackPlanGen
  list rich_list stackModel stackPlanOps stackPlanTypes fnPlanLineagePhiTemporal
  fnPlanLineageInventory

(* Backwards transfer and forward execution are intentionally separate.
   The latter never replaces an intermediate state by a canonical stack. *)
Definition assign_region_live_def:
  assign_region_live schedule exit =
    FOLDR (\ay nl. liveness_transfer [] (canonical_assign (FST ay) (SND ay)) nl)
      exit schedule
End

Definition assign_region_ready_def:
  assign_region_ready schedule <=>
    EVERY (\ay. FST ay <> SND ay) schedule /\
    ALL_DISTINCT (MAP SND schedule) /\
    (!i j. i <= j /\ j < LENGTH schedule ==>
      FST (EL i schedule) <> SND (EL j schedule))
End

Definition assign_region_step_def:
  assign_region_step liveness dfg cfg fn lbl a y nl term ps =
    SND (generate_regular_inst_plan liveness dfg cfg fn
      (canonical_assign a y) nl F term lbl ps)
End

(* Every call is the full nonhalting regular transition. For a straight-line
   ASSIGN suffix, next_is_terminator is false, including the last observation.
   This is the query-active branch rather than a terminator skip. *)
Definition assign_region_safe_def:
  (assign_region_safe liveness dfg cfg fn lbl [] exit ps = T) /\
  (assign_region_safe liveness dfg cfg fn lbl (ay::rest) exit ps =
    ((assign_region_live rest exit <> [] /\
      SND ay <> LAST (assign_region_live rest exit) ==>
      MEM (Var (LAST (assign_region_live rest exit)))
        (canonical_assign_observe dfg (FST ay) (SND ay)
          (assign_region_live rest exit) ps).ps_stack) /\
     assign_region_safe liveness dfg cfg fn lbl rest exit
       (assign_region_step liveness dfg cfg fn lbl (FST ay) (SND ay)
         (assign_region_live rest exit) F ps)))
End

Theorem assign_region_live_cons:
  assign_region_live (ay::rest) exit =
    liveness_transfer [] (canonical_assign (FST ay) (SND ay))
      (assign_region_live rest exit)
Proof
  simp[assign_region_live_def]
QED

Theorem assign_region_step_postprocess:
  !liveness dfg cfg fn lbl a y nl term ps.
    assign_region_step liveness dfg cfg fn lbl a y nl term ps =
      release_dead_spills nl
        (if MEM y nl then
          SND (optimistic_swap_plan dfg (canonical_assign a y) nl term
            (canonical_assign_observe dfg a y nl ps))
         else canonical_assign_observe dfg a y nl ps)
Proof
  rpt gen_tac >>
  simp[assign_region_step_def, lineage_regular_prepare_decompose,
    canonical_assign_def, mk_inst_def] >>
  simp[canonical_assign_observe_def, canonical_assign_def, mk_inst_def] >>
  Cases_on `MEM y nl` >> simp[] >>
  simp[pairTheory.pair_CASE_def, pairTheory.UNCURRY]
QED

(* This is only the initialized induction equation. Its RHS deliberately
   retains the full native successor state, not MAP Var of the next list. *)
Theorem assign_region_canonical_head:
  !liveness dfg cfg fn lbl a y rest exit ps.
    a <> y /\
    ps.ps_stack = MAP Var (assign_region_live ((a,y)::rest) exit) /\
    ps.ps_spilled = FEMPTY ==>
    (assign_region_safe liveness dfg cfg fn lbl ((a,y)::rest) exit ps =
     assign_region_safe liveness dfg cfg fn lbl rest exit
       (assign_region_step liveness dfg cfg fn lbl a y
         (assign_region_live rest exit) F ps))
Proof
  rpt strip_tac >>
  gvs[assign_region_live_cons] >>
  `!dfg. (canonical_assign_observe dfg a y (assign_region_live rest exit) ps).ps_stack =
    MAP Var (FILTER (\v. v <> y) (assign_region_live rest exit)) ++
      (if MEM y (assign_region_live rest exit) then [Var y] else [])` by
    metis_tac[canonical_assign_observe_stack] >>
  simp[assign_region_safe_def] >>
  Cases_on `assign_region_live rest exit = []` >- simp[] >>
  Cases_on `y = LAST (assign_region_live rest exit)` >- simp[] >>
  simp[MEM_MAP, MEM_FILTER, LAST_MEM]
QED

(* A candidate physical boundary: all live values occur exactly once on the
   stack, but their order is retained from native execution, not reset. *)
Definition assign_region_physical_def:
  assign_region_physical nl ps <=>
    ALL_DISTINCT ps.ps_stack /\
    (!op. MEM op ps.ps_stack <=> MEM op (MAP Var nl)) /\
    ps.ps_spilled = FEMPTY
End

Theorem assign_region_physical_init:
  !nl ps. ALL_DISTINCT nl /\ ps.ps_stack = MAP Var nl /\
    ps.ps_spilled = FEMPTY ==> assign_region_physical nl ps
Proof
  rpt strip_tac >> simp[assign_region_physical_def] >>
  irule ALL_DISTINCT_MAP_INJ >> simp[]
QED

(* A dead, last-use ASSIGN does not duplicate its input and skips optimistic
   swap. This exposes the actual reorder rather than a canonical successor. *)
Theorem assign_region_dead_prepare:
  !dfg a y nl ps.
    ~MEM a nl /\ FLOOKUP ps.ps_spilled (Var a) = NONE ==>
    (SND (lineage_regular_prepare dfg (canonical_assign a y) nl ps)).ps_stack =
      stack_pop 1 (SND (reorder_plan dfg [Var a] ps)).ps_stack ++ [Var y]
Proof
  rpt strip_tac >>
  simp[lineage_regular_prepare_def, canonical_assign_def, mk_inst_def,
    compute_operands_def, python_stack_operands_def, emit_input_plan_one,
    emit_one_input_def, is_var_operand_def, stack_push_def] >>
  Cases_on `reorder_plan dfg [Var a] ps` >> simp[] >>
  simp[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name ASSIGN` >> simp[]
QED

Theorem assign_region_dead_step_stack:
  !liveness dfg cfg fn lbl a y nl term ps.
    ~MEM a nl /\ ~MEM y nl /\
    FLOOKUP ps.ps_spilled (Var a) = NONE ==>
    (assign_region_step liveness dfg cfg fn lbl a y nl term ps).ps_stack =
      stack_pop 1 (SND (reorder_plan dfg [Var a] ps)).ps_stack
Proof
  rpt strip_tac >> simp[assign_region_step_postprocess] >>
  simp[release_dead_spills_stack] >>
  drule_all assign_region_dead_prepare >> strip_tac >>
  qabbrev_tac `qs = SND (lineage_regular_prepare dfg (canonical_assign a y) nl ps)` >>
  `qs.ps_stack = stack_pop 1 (SND (reorder_plan dfg [Var a] ps)).ps_stack ++ [Var y]` by
    simp[Abbr `qs`] >>
  `stack_get_depth (Var y) qs.ps_stack = SOME 0` by
    simp[stack_get_depth_def, REVERSE_APPEND, stack_find_def] >>
  drule popmany_singleton_stack_projection >>
  simp[canonical_assign_observe_def, Abbr `qs`] >>
  simp[stack_swap_def, stack_pop_def, LUPDATE_SAME,
    TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

