Theory fnLineageInvDFSResources
Ancestors fnLineageInvOwnerOrigin fnLineageInvBoundary reorderSim planSpillBounds list

Theorem residual_budget_wf_alloc_extension:
  !base pending A D.
    residual_budget_wf base pending A /\
    D.ps_stack = A.ps_stack /\ D.ps_spilled = A.ps_spilled /\
    D.ps_alloc.sa_spill_base = A.ps_alloc.sa_spill_base /\
    D.ps_alloc.sa_free_slots = A.ps_alloc.sa_free_slots /\
    A.ps_alloc.sa_next_offset <= D.ps_alloc.sa_next_offset ==>
    residual_budget_wf base pending D
Proof
  rpt gen_tac >> strip_tac >>
  `spill_alloc_layout_wf D.ps_alloc D.ps_spilled` by
    (irule spill_alloc_layout_wf_extension >>
     qexists_tac `A.ps_alloc` >> gvs[residual_budget_wf_def]) >>
  gvs[residual_budget_wf_def, plan_slots_bounded_def,
      alloc_slots_bounded_def, EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
