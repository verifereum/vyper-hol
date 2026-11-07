Theory fnPlanLineagePhysical
Ancestors fnPlanLineageAssignRegion fnPlanLineageInventory fnPlanLineagePhysicalOps stackPlanTypes
  stackPlanGen stackPlanOps stackModel list pred_set finite_map
  fnPlanLineageCanonicalAssign fnPlanLineageSetup venomInst

(* Reuse the existing exact inventory rather than introduce a second copy.
   The extra spill-variable condition is redundant when S is MAP Var live. *)
Definition physical_live_def:
  physical_live live ps <=> lineage_inventory (set (MAP Var live)) ps
End

Theorem physical_live_init:
  !live ps m.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ MAP Var live /\
    ALL_DISTINCT live /\ ps.ps_spilled = FEMPTY ==> physical_live live ps
Proof
  rpt strip_tac >>
  simp[physical_live_def, lineage_inventory_def, lineage_core_def] >>
  qexistsl [`m`, `MAP Var live`] >>
  simp[EVERY_MAP, is_var_operand_def] >>
  irule ALL_DISTINCT_MAP_INJ >> simp[]
QED

Theorem physical_live_explicit:
  !live ps. physical_live live ps <=>
    ?m names.
      ps.ps_stack = REPLICATE m dead_stack_marker ++ MAP Var names /\
      ALL_DISTINCT names /\
      DISJOINT (set (MAP Var names)) (FDOM ps.ps_spilled) /\
      set (MAP Var names) UNION FDOM ps.ps_spilled = set (MAP Var live)
Proof
  rpt gen_tac >> simp[physical_live_def, lineage_inventory_def, lineage_core_def] >>
  eq_tac
  >- (rpt strip_tac >>
      `?names. core = MAP Var names` by
        (qpat_x_assum `EVERY is_var_operand core` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         Induct_on `core` >> simp[] >>
         Cases_on `h` >> simp[is_var_operand_def] >>
         strip_tac >> first_x_assum drule >> strip_tac >>
         qexists `s::names` >> simp[]) >>
      gvs[] >> qexistsl [`m`, `names`] >> simp[EVERY_MAP, is_var_operand_def] >>
      qpat_x_assum `ALL_DISTINCT (MAP Var names)` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `names` >> simp[MEM_MAP]) >>
  rpt strip_tac >> qexistsl [`m`, `MAP Var names`] >>
  simp[EVERY_MAP, is_var_operand_def] >> conj_tac
  >- (irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  rpt strip_tac >>
  `MEM op (MAP Var live)` by ASM_SET_TAC[] >>
  gvs[MEM_MAP, is_var_operand_def]
QED

(* Native last-use emission restores a spilled source but does not duplicate
   it. No allocator-layout premise is needed at this boundary. *)
Theorem physical_live_emit_dead_source:
  !a nl ps.
    ~MEM a nl /\ physical_live (a::nl) ps ==>
    physical_live (a::nl) (SND (emit_one_input ASSIGN nl (Var a) ps))
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP ps.ps_spilled (Var a)` >>
  gvs[physical_live_def, emit_one_input_def, is_var_operand_def] >>
  Cases_on `do_restore (Var a) ps` >>
  gvs[] >> metis_tac[do_restore_lineage_inventory, pairTheory.SND]
QED

Theorem physical_live_reorder_singleton:
  !live dfg a ps.
    physical_live live ps ==>
    physical_live live (SND (reorder_plan dfg [Var a] ps))
Proof
  simp[physical_live_def, reorder_singleton_lineage_inventory]
QED

Theorem physical_live_emit_dead_source_available:
  !a nl ps.
    ~MEM a nl /\ physical_live (a::nl) ps ==>
    ?d. stack_get_depth (Var a)
          (SND (emit_one_input ASSIGN nl (Var a) ps)).ps_stack = SOME d /\
        FLOOKUP (SND (emit_one_input ASSIGN nl (Var a) ps)).ps_spilled
          (Var a) = NONE
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP ps.ps_spilled (Var a)`
  >- (`MEM (Var a) ps.ps_stack` by
        (gvs[physical_live_explicit, FLOOKUP_DEF] >> ASM_SET_TAC[]) >>
      `IS_SOME (stack_get_depth (Var a) ps.ps_stack)` by
        simp[stack_get_depth_is_some] >>
      simp[emit_one_input_def, is_var_operand_def] >>
      Cases_on `stack_get_depth (Var a) ps.ps_stack` >> gvs[]) >>
  simp[emit_one_input_def, is_var_operand_def, stackPlanOpsTheory.do_restore_def,
    stack_push_def, stack_get_depth_def, REVERSE_SNOC, stack_find_def]
QED

Theorem physical_live_consume_dead_source:
  !dfg a nl ps.
    ~MEM a nl /\ physical_live (a::nl) ps /\
    IS_SOME (stack_get_depth (Var a) ps.ps_stack) ==>
    physical_live nl
      ((SND (reorder_plan dfg [Var a] ps)) with ps_stack :=
        stack_pop 1 (SND (reorder_plan dfg [Var a] ps)).ps_stack)
Proof
  rpt strip_tac >>
  `IS_SOME (stack_get_unfixed_depth (Var a) 0 1 ps.ps_stack)` by
    simp[stack_get_unfixed_depth_def] >>
  drule reorder_singleton_source_top >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by
    (Cases_on `stack_get_depth (Var a) ps.ps_stack` >> gvs[] >>
     drule stack_get_depth_props >> simp[]) >>
  qabbrev_tac `qs = SND (reorder_plan dfg [Var a] ps)` >>
  `1 <= LENGTH qs.ps_stack` by
    (qspec_then `dfg` mp_tac reorder_one_length_floor >>
     disch_then (qspecl_then [`[Var a]`, `0`, `Var a`, `ps`] mp_tac) >>
     simp[Abbr `qs`, reorder_plan_def, indexedListsTheory.MAPi_def] >>
     Cases_on `reorder_one dfg [Var a] 0 (Var a) ps` >> simp[]) >>
  `lineage_inventory (set (MAP Var (a::nl))) qs` by
    simp[Abbr `qs`, GSYM physical_live_def, physical_live_reorder_singleton] >>
  `stack_get_depth (Var a) qs.ps_stack = SOME 0` by
    (irule lineage_inventory_variable_peek_lookup >>
     simp[] >> reverse conj_tac >- metis_tac[] >> simp[Abbr `qs`]) >>
  `MEM (Var a) qs.ps_stack` by
    metis_tac[stack_get_depth_is_some, optionTheory.IS_SOME_DEF] >>
  drule_at (Pat `lineage_inventory _ _`) popmany_plan_lineage_inventory >>
  disch_then (qspec_then `[Var a]` mp_tac) >>
  simp[dead_stack_marker_def, popmany_plan_top_singleton] >>
  `set (MAP Var (a::nl)) DIFF {Var a} = set (MAP Var nl)` by
    (simp[EXTENSION, MEM_MAP] >> gen_tac >> Cases_on `x` >> simp[] >>
     metis_tac[]) >>
  `set (MAP Var nl) DIFF ({Var a} INTER set qs.ps_stack) =
    set (MAP Var nl)` by
    ( `Var a NOTIN set (MAP Var nl)` by simp[MEM_MAP] >> ASM_SET_TAC[]) >>
  simp[physical_live_def]
QED

Theorem native_assign_prepare_state:
  !dfg a y nl ps.
    SND (lineage_regular_prepare dfg (canonical_assign a y) nl ps) =
      (SND (reorder_plan dfg [Var a]
        (SND (emit_one_input ASSIGN nl (Var a) ps)))) with ps_stack :=
          stack_pop 1 (SND (reorder_plan dfg [Var a]
            (SND (emit_one_input ASSIGN nl (Var a) ps)))).ps_stack ++ [Var y]
Proof
  rpt gen_tac >>
  simp[lineage_regular_prepare_def, canonical_assign_def, mk_inst_def,
    compute_operands_def, python_stack_operands_def, emit_input_plan_one] >>
  Cases_on `emit_one_input ASSIGN nl (Var a) ps` >> simp[] >>
  Cases_on `reorder_plan dfg [Var a] r` >> simp[] >>
  simp[stack_push_def, SNOC_APPEND, generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name ASSIGN` >> simp[]
QED

Theorem native_dead_assign_state:
  !liveness dfg cfg fn lbl a y nl term ps.
    ~MEM y nl ==>
    assign_region_step liveness dfg cfg fn lbl a y nl term ps =
      release_dead_spills nl
        ((SND (reorder_plan dfg [Var a]
            (SND (emit_one_input ASSIGN nl (Var a) ps)))) with ps_stack :=
          stack_pop 1 (SND (reorder_plan dfg [Var a]
            (SND (emit_one_input ASSIGN nl (Var a) ps)))).ps_stack)
Proof
  rpt strip_tac >>
  simp[assign_region_step_postprocess, canonical_assign_observe_def,
    native_assign_prepare_state, canonical_assign_def, mk_inst_def] >>
  simp[popmany_plan_top_singleton, stack_get_depth_def, REVERSE_APPEND,
    stack_find_def, stack_pop_def, rich_listTheory.TAKE_APPEND,
    rich_listTheory.TAKE_TAKE]
QED

Theorem physical_live_release_dead_spills:
  !nl ps. physical_live nl ps ==> physical_live nl (release_dead_spills nl ps)
Proof
  rpt gen_tac >> simp[physical_live_def, lineage_inventory_def, lineage_core_def] >>
  strip_tac >> qexistsl [`m`, `core`] >>
  simp[release_dead_spills_stack, release_dead_spills_domain] >>
  ASM_SET_TAC[]
QED

Theorem physical_live_native_dead_assign:
  !liveness dfg cfg fn lbl a y nl term ps.
    ~MEM a nl /\ ~MEM y nl /\ physical_live (a::nl) ps ==>
    physical_live nl
      (assign_region_step liveness dfg cfg fn lbl a y nl term ps)
Proof
  rpt strip_tac >> simp[native_dead_assign_state] >>
  irule physical_live_release_dead_spills >>
  irule physical_live_consume_dead_source >> simp[] >>
  conj_tac
  >- (drule_all physical_live_emit_dead_source_available >> strip_tac >> simp[]) >>
  simp[physical_live_emit_dead_source]
QED

Theorem physical_live_push_fresh:
  !live y ps.
    ~MEM y live /\ physical_live live ps ==>
    physical_live (y::live) (ps with ps_stack := stack_push (Var y) ps.ps_stack)
Proof
  rpt gen_tac >> simp[physical_live_explicit] >> rpt strip_tac >>
  `~MEM y names /\ Var y NOTIN FDOM ps.ps_spilled` by
    ( `Var y NOTIN set (MAP Var live)` by simp[MEM_MAP] >>
      `Var y NOTIN FDOM ps.ps_spilled` by ASM_SET_TAC[] >>
      `~MEM (Var y) (MAP Var names)` by ASM_SET_TAC[] >>
      gvs[MEM_MAP]) >>
  qexistsl [`m`, `names ++ [y]`] >>
  simp[stack_push_def, SNOC_APPEND, APPEND_ASSOC, MAP_APPEND,
    ALL_DISTINCT_APPEND, DISJOINT_DEF, EXTENSION] >>
  ASM_SET_TAC[]
QED

Theorem physical_live_native_live_assign_from_consumed:
  !liveness dfg cfg fn lbl a y nl term ps.
    MEM y nl /\
    physical_live (FILTER (\v. v <> y) nl)
      ((SND (reorder_plan dfg [Var a]
        (SND (emit_one_input ASSIGN nl (Var a) ps)))) with ps_stack :=
        stack_pop 1 (SND (reorder_plan dfg [Var a]
          (SND (emit_one_input ASSIGN nl (Var a) ps)))).ps_stack) ==>
    physical_live nl
      (assign_region_step liveness dfg cfg fn lbl a y nl term ps)
Proof
  rpt strip_tac >>
  drule_at (Pat `physical_live _ _`) physical_live_push_fresh >>
  disch_then (qspec_then `y` mp_tac) >> simp[MEM_FILTER] >> strip_tac >>
  `set (MAP Var (y::FILTER (\v. v <> y) nl)) = set (MAP Var nl)` by
    (simp[EXTENSION, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  `physical_live nl (SND (lineage_regular_prepare dfg (canonical_assign a y) nl ps))` by
    gvs[physical_live_def, native_assign_prepare_state, stack_push_def, SNOC_APPEND] >>
  simp[assign_region_step_postprocess, canonical_assign_observe_def,
    canonical_assign_def, mk_inst_def, popmany_plan_def] >>
  irule physical_live_release_dead_spills >>
  simp[physical_live_def] >> irule optimistic_swap_plan_lineage_inventory >>
  gvs[physical_live_def, canonical_assign_def, mk_inst_def]
QED

Theorem physical_live_native_live_lastuse_assign:
  !liveness dfg cfg fn lbl a y nl term ps.
    ~MEM a nl /\ MEM y nl /\
    physical_live (a::FILTER (\v. v <> y) nl) ps ==>
    physical_live nl
      (assign_region_step liveness dfg cfg fn lbl a y nl term ps)
Proof
  rpt strip_tac >>
  `~MEM a (FILTER (\v. v <> y) nl)` by simp[MEM_FILTER] >>
  `emit_one_input ASSIGN nl (Var a) ps =
    emit_one_input ASSIGN (FILTER (\v. v <> y) nl) (Var a) ps` by
    simp[emit_one_input_def, is_var_operand_def, MEM_FILTER] >>
  `physical_live (FILTER (\v. v <> y) nl)
    ((SND (reorder_plan dfg [Var a]
      (SND (emit_one_input ASSIGN nl (Var a) ps)))) with ps_stack :=
      stack_pop 1 (SND (reorder_plan dfg [Var a]
        (SND (emit_one_input ASSIGN nl (Var a) ps)))).ps_stack)` by
    (asm_rewrite_tac[] >> irule physical_live_consume_dead_source >> simp[] >>
     conj_tac
     >- (drule_all physical_live_emit_dead_source_available >> strip_tac >> simp[]) >>
     simp[physical_live_emit_dead_source]) >>
  irule physical_live_native_live_assign_from_consumed >> simp[]
QED

Theorem reorder_plan_dup_singleton:
  !dfg a ps d.
    stack_peek d ps.ps_stack = Var a ==>
    reorder_plan dfg [Var a] (SND (do_dup d ps)) =
      ([], SND (do_dup d ps))
Proof
  rpt strip_tac >> irule reorder_plan_singleton_top >>
  simp[do_dup_def] >> Cases_on `d <= 15` >> simp[stack_dup_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[stack_dup_def]
QED

Theorem physical_live_consume_live_source:
  !dfg a nl live ps.
    MEM a nl /\ MEM a live /\ physical_live live ps ==>
    physical_live live
      ((SND (reorder_plan dfg [Var a]
        (SND (emit_one_input ASSIGN nl (Var a) ps)))) with ps_stack :=
        stack_pop 1 (SND (reorder_plan dfg [Var a]
          (SND (emit_one_input ASSIGN nl (Var a) ps)))).ps_stack)
Proof
  rpt strip_tac >>
  qabbrev_tac `rs = SND (do_restore (Var a) ps)` >>
  `physical_live live rs` by
    (gvs[physical_live_def] >> simp[Abbr `rs`, do_restore_lineage_inventory]) >>
  `MEM (Var a) rs.ps_stack` by
    (Cases_on `FLOOKUP ps.ps_spilled (Var a)` >>
     gvs[Abbr `rs`, do_restore_def, stack_push_def, SNOC_APPEND] >>
     gvs[physical_live_explicit, FLOOKUP_DEF] >>
     `MEM (Var a) (MAP Var live)` by simp[MEM_MAP] >> ASM_SET_TAC[]) >>
  `IS_SOME (stack_get_depth (Var a) rs.ps_stack)` by
    simp[stack_get_depth_is_some] >>
  Cases_on `stack_get_depth (Var a) rs.ps_stack` >> gvs[] >>
  `stack_peek x rs.ps_stack = Var a` by
    metis_tac[stack_get_depth_props] >>
  `SND (emit_one_input ASSIGN nl (Var a) ps) = SND (do_dup x rs)` by
    (Cases_on `FLOOKUP ps.ps_spilled (Var a)` >>
     gvs[emit_one_input_def, is_var_operand_def, Abbr `rs`, do_restore_def] >>
     rpt (pairarg_tac >> gvs[])) >>
  simp[reorder_plan_dup_singleton] >>
  gvs[physical_live_def] >> irule do_dup_consume_lineage_inventory >> simp[]
QED

Theorem physical_live_native_dead_output_live_source_assign:
  !liveness dfg cfg fn lbl a y nl term ps.
    a <> y /\ MEM a nl /\ ~MEM y nl /\ physical_live nl ps ==>
    physical_live nl
      (assign_region_step liveness dfg cfg fn lbl a y nl term ps)
Proof
  rpt strip_tac >> simp[native_dead_assign_state] >>
  irule physical_live_release_dead_spills >>
  irule physical_live_consume_live_source >> simp[] >> metis_tac[]
QED

Theorem physical_live_native_live_output_live_source_assign:
  !liveness dfg cfg fn lbl a y nl term ps.
    a <> y /\ MEM a nl /\ MEM y nl /\
    physical_live (FILTER (\v. v <> y) nl) ps ==>
    physical_live nl
      (assign_region_step liveness dfg cfg fn lbl a y nl term ps)
Proof
  rpt strip_tac >> irule physical_live_native_live_assign_from_consumed >> simp[] >>
  irule physical_live_consume_live_source >> simp[MEM_FILTER] >> metis_tac[]
QED
