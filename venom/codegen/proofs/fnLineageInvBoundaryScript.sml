Theory fnLineageInvBoundary
Ancestors fnPlanPrefix fnPlanLineageInventory list pred_set

Theorem lineage_inventory_live_membership:
  !vs ps. lineage_inventory (set (MAP Var vs)) ps ==>
    (!op. (MEM op ps.ps_stack /\ op <> dead_stack_marker) \/
          op IN FDOM ps.ps_spilled ==> ?v. op = Var v /\ MEM v vs) /\
    (!v. MEM v vs ==> MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule lineage_inventory_stack_subset >>
      drule lineage_inventory_spilled_subset >>
      simp[pred_setTheory.SUBSET_DEF, MEM_MAP] >> metis_tac[]) >>
  gvs[lineage_inventory_def, lineage_core_def,
      pred_setTheory.EXTENSION, MEM_MAP] >>
  metis_tac[MEM_APPEND, pred_setTheory.IN_UNION]
QED
