Theory concretizeAnalysisMetadataOwnership
Ancestors
  concretizeAnalysisMetadata concretizeAnalysisOwnership
  concretizeAnalysisMetadataSchedule staticLayoutAllocatorProofs
  concretizeStageLookup concretizeMemLocDefs list

Theorem static_alloca_items_source_owns:
  MEM fn C.ctx_functions /\ static_alloca_items fn = SOME items ==>
  EVERY (\(a,s). source_owns C fn a s) items
Proof
  strip_tac >> simp[EVERY_MEM] >> PairCases >> strip_tac >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(e0,e1)` mp_tac) >> simp[] >> strip_tac >>
  gvs[exact_static_alloca_def, exact_static_alloca_size_def, AllCaseEqs()] >>
  metis_tac[source_owns_literal]
QED

Theorem concretize_context_source_owns:
  MEM fn C.ctx_functions /\ fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel observed reserved fn = SOME out /\
  (!inst name args g.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label name :: args /\
    lookup_function name observed.ctx_functions = SOME g ==>
    EVERY (\(a,p,s). source_owns C fn a s) g.fn_mems_used) ==>
  EVERY (\(a,p,s). source_owns C fn a s) out.fn_mems_used
Proof
  strip_tac >>
  `EVERY (\(a,p,s). source_owns C fn a s) (imported_mems_used observed fn)` by
    (irule imported_mems_used_every >> metis_tac[]) >>
  drule_all concretize_context_rebuilds_metadata >> strip_tac >> gvs[] >>
  Cases_on `static_alloca_items fn`
  >- (simp[apply_context_concretize_layout_def] >>
      irule unique_mems_used_every >> simp[]) >>
  irule apply_context_layout_mems_every >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all static_alloca_items_source_owns >>
  simp[EVERY_MEM] >> metis_tac[]
QED
