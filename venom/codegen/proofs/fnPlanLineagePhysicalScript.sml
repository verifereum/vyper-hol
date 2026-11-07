Theory fnPlanLineagePhysical
Ancestors fnPlanLineageAssignRegion fnPlanLineageInventory fnPlanLineagePhysicalOps stackPlanTypes
  stackPlanGen stackModel list pred_set finite_map

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
