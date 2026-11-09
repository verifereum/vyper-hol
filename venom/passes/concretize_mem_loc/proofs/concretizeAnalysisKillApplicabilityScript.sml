Theory concretizeAnalysisKillApplicability
Ancestors
  concretizeAnalysisExclusiveWriters concretizeAnalysisExclusiveSources
  concretizePtrBPOrigins concretizePtrReadCoverage concretizeAnalysisWriteSafety
  concretizeAnalysisRoots pointerClosure pointerConfinedDefs ptrDiscipline
  basePtrDefs memLocDefs concretizeMemLocDefs concretizeAnalysisBoundary
  venomInst pred_set list

Theorem ptr_bp_alloc_roots_subset[local]:
  ptr_bp_alloc_roots fn aid SUBSET alloca_roots fn
Proof
  simp[ptr_bp_alloc_roots_def, alloca_roots_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem production_write_allocation_exclusive:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  MEM (Ptr (Allocation aid) off) (bp_get_ptrs (bp_analyze_fuel fuel cfg fn) v) ==>
  allocation_exclusive P fn v
Proof
  strip_tac >> drule ptr_bp_analyze_origins >> strip_tac >>
  `FINITE (alloca_roots fn)` by
    (irule SUBSET_FINITE >> qexists_tac `ptr_roots P fn` >>
     simp[ptr_roots_finite, ptr_roots_def, SUBSET_DEF]) >>
  `pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) SUBSET
   pointer_derived_vars fn (alloca_roots fn)` by
    (irule ptr_derived_mono >> simp[ptr_bp_alloc_roots_finite, ptr_bp_alloc_roots_subset]) >>
  `v IN pointer_derived_vars fn (alloca_roots fn)` by fs[SUBSET_DEF] >>
  simp[allocation_exclusive_def] >> metis_tac[write_allocation_exclusive]
QED

Theorem production_kill_allocation_exclusive:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  ptr_ml_can_kill (Allocation aid) (bp_analyze_fuel fuel cfg fn) sizes inst ==>
  allocation_exclusive P fn v
Proof
  strip_tac >>
  `MEM (Allocation aid) (find_base_allocas (bp_analyze_fuel fuel cfg fn) (Var v))` by
    gvs[ptr_ml_can_kill_def, inst_write_op_def, find_base_allocas_opt_def] >>
  gvs[GSYM bp_bases_find_base_allocas, bp_bases_def, MEM_MAP] >>
  Cases_on `y` >> gvs[ptr_base_def] >>
  drule_all production_write_allocation_exclusive >> simp[]
QED
