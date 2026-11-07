Theory fnPlanLineageAssignRegion
Ancestors fnPlanLineageCanonicalAssign fnPlanLineageSetup venomInst stackPlanGen
  list rich_list

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
