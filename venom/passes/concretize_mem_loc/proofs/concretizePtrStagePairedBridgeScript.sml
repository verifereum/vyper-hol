Theory concretizePtrStagePairedBridge
Ancestors
  concretizePtrStagePlacements concretizePtrExecutedCoverage
  staticLayoutAllocatorProofs concretizeStageShape concretizePtrPairedFields
  concretizeStepStructure venomInst list finite_map

Theorem ptr_layout_stage_lookup:
  ptr_stage_placements C' positions /\ MEM g C'.ctx_functions /\
  f.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved f = SOME g /\
  g = apply_context_concretize_layout ctx layout f /\
  (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP layout.cl_positions (Allocation i.inst_id))) ==>
  !bb i. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = ALLOCA ==>
    FLOOKUP layout.cl_positions (Allocation i.inst_id) =
      OPTION_MAP FST (FLOOKUP positions (Allocation i.inst_id))
Proof
  strip_tac >>
  drule_all ptr_concretize_static_items >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `MEM i (fn_insts f)` by
    (simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  rename1 `exact_static_alloca i = SOME (Allocation i.inst_id,w2n n)` >>
  `MEM (Allocation i.inst_id,w2n n) items` by
    (drule static_alloca_items_MEM >> metis_tac[]) >>
  `IS_SOME (FLOOKUP layout.cl_positions (Allocation i.inst_id))` by
    metis_tac[] >>
  Cases_on `FLOOKUP layout.cl_positions (Allocation i.inst_id)` >> gvs[] >>
  `MEM (Allocation i.inst_id,x,w2n n)
     (apply_context_concretize_layout ctx layout f).fn_mems_used` by
    (drule_all ptr_layout_own_mems >>
     disch_then (qspecl_then [`layout`,`ctx`] mp_tac) >> simp[]) >>
  `FLOOKUP positions (Allocation i.inst_id) = SOME (x,w2n n)` by
    (fs[ptr_stage_placements_def] >> metis_tac[]) >>
  simp[]
QED
