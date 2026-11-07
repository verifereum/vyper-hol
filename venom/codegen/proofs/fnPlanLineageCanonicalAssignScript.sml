Theory fnPlanLineageCanonicalAssign
Ancestors fnPlanLineageSetup livenessDefs venomInst stackModel list rich_list
  stackPlanGen stackPlanTypes fnPlanLineageInventory dfgDefs finite_map
  fnPlanLineagePhiTemporal
Libs stackPlanOpsTheory doSwapSimTheory

Definition canonical_assign_def:
  canonical_assign a y = mk_inst 0 ASSIGN [Var a] [y]
End
Definition canonical_assign_observe_def:
  canonical_assign_observe dfg a y nl ps =
    SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) [y]))
      (SND (lineage_regular_prepare dfg (canonical_assign a y) nl ps)))
End

Theorem reorder_plan_singleton_top:
  !dfg op ps stk.
    ps.ps_stack = SNOC op stk ==> reorder_plan dfg [op] ps = ([],ps)
Proof
  rpt strip_tac >>
  simp[reorder_plan_def, reorder_one_def, stack_get_unfixed_depth_def,
    stack_get_depth_def, REVERSE_SNOC, stack_find_def]
QED

Theorem canonical_assign_live_update:
  !a y nl. a <> y ==>
    liveness_transfer [] (canonical_assign a y) nl =
      if MEM a nl then FILTER (\v. v <> y) nl
      else FILTER (\v. v <> y) nl ++ [a]
Proof
  rpt strip_tac >>
  simp[canonical_assign_def, mk_inst_def, liveness_transfer_def,
    live_update_def, inst_defs_def, ordered_inst_uses_def,
    python_stack_operands_def, venomInstTheory.operand_vars_def,
    dfgDefsTheory.operand_vars_def, venomInstTheory.operand_var_def,
    dfgDefsTheory.operand_var_def, MEM_FILTER] >>
  metis_tac[]
QED

Theorem emit_live_var_stack:
  !opc a nl ps.
    MEM a nl /\ MEM (Var a) ps.ps_stack /\
    FLOOKUP ps.ps_spilled (Var a) = NONE ==>
    (SND (emit_one_input opc nl (Var a) ps)).ps_stack =
      SNOC (Var a) ps.ps_stack
Proof
  rpt strip_tac >>
  `IS_SOME (stack_get_depth (Var a) ps.ps_stack)` by
    simp[stack_get_depth_is_some] >>
  Cases_on `stack_get_depth (Var a) ps.ps_stack` >> gvs[] >>
  drule stack_get_depth_props >> strip_tac >>
  simp[emit_one_input_def, is_var_operand_def] >>
  drule do_dup_stack_exact >> simp[SNOC_APPEND] >>
  Cases_on `do_dup x ps` >> simp[]
QED

Theorem canonical_assign_prepare_stack:
  !dfg a y nl ps.
    a <> y /\
    ps.ps_stack = MAP Var (liveness_transfer [] (canonical_assign a y) nl) /\
    ps.ps_spilled = FEMPTY ==>
    (SND (lineage_regular_prepare dfg (canonical_assign a y) nl ps)).ps_stack =
      MAP Var (FILTER (\v. v <> y) nl) ++ [Var y]
Proof
  rpt strip_tac >>
  gvs[canonical_assign_live_update] >>
  `MEM a nl ==> MEM (Var a) ps.ps_stack` by
    (strip_tac >> gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  `(SND (emit_one_input ASSIGN nl (Var a) ps)).ps_stack =
     SNOC (Var a) (MAP Var (FILTER (\v. v <> y) nl))` by
    (Cases_on `MEM a nl`
     >- (gvs[] >> metis_tac[emit_live_var_stack, FLOOKUP_EMPTY])
     >> gvs[emit_one_input_def, is_var_operand_def, MAP_APPEND, SNOC_APPEND]) >>
  Cases_on `emit_one_input ASSIGN nl (Var a) ps` >> gvs[] >>
  `reorder_plan dfg [Var a] r = ([],r)` by
    (irule reorder_plan_singleton_top >> simp[SNOC_APPEND]) >>
  simp[lineage_regular_prepare_def, canonical_assign_def, mk_inst_def,
    compute_operands_def, python_stack_operands_def, emit_input_plan_one,
    generate_emit_ops_def, stack_pop_def, stack_push_def] >>
  Cases_on `venom_to_evm_name ASSIGN` >> simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, SNOC_APPEND]
QED

Theorem canonical_assign_observe_stack:
  !dfg a y nl ps.
    a <> y /\
    ps.ps_stack = MAP Var (liveness_transfer [] (canonical_assign a y) nl) /\
    ps.ps_spilled = FEMPTY ==>
    (canonical_assign_observe dfg a y nl ps).ps_stack =
      MAP Var (FILTER (\v. v <> y) nl) ++
        (if MEM y nl then [Var y] else [])
Proof
  rpt strip_tac >>
  qspec_then `dfg` (drule_all_then assume_tac) canonical_assign_prepare_stack >>
  qabbrev_tac `qs = SND (lineage_regular_prepare dfg (canonical_assign a y) nl ps)` >>
  `qs.ps_stack = MAP Var (FILTER (\v. v <> y) nl) ++ [Var y]` by
    simp[Abbr `qs`] >>
  Cases_on `MEM y nl`
  >- simp[canonical_assign_observe_def, popmany_plan_def, Abbr `qs`] >>
  `stack_get_depth (Var y) qs.ps_stack = SOME 0` by
    simp[stack_get_depth_def, REVERSE_APPEND, stack_find_def] >>
  drule popmany_singleton_stack_projection >>
  simp[canonical_assign_observe_def, Abbr `qs`, stack_swap_def,
    stack_pop_def, LUPDATE_SAME, TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

Theorem canonical_assign_observe_last:
  !dfg a y nl ps.
    ALL_DISTINCT nl /\ a <> y /\ nl <> [] /\ y <> LAST nl /\
    ps.ps_stack = MAP Var (liveness_transfer [] (canonical_assign a y) nl) /\
    ps.ps_spilled = FEMPTY ==>
    MEM (Var (LAST nl)) (canonical_assign_observe dfg a y nl ps).ps_stack
Proof
  rpt strip_tac >>
  drule_all canonical_assign_observe_stack >> strip_tac >>
  simp[MEM_MAP, MEM_FILTER, LAST_MEM]
QED
