Theory concretizePtrSingletonSite
Ancestors concretizePtrFrameOrigins concretizePtrBPReverse concretizePtrClosure
  concretizePtrRuntimeOrigins concretizePtrProductionCoverage
  concretizeAnalysisScanCoverage cfgAnalysisProps venomWf cfgWf concretizeMemLocDefs
  concretizeAnalysisRoots ptrDiscipline pointerConfinedDefs pointerClosure
  concretizePtrBPOrigins basePtrDefs venomInst finite_map pred_set list

Theorem ptr_covered_singleton_write_site:
  fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) /\
  ptr_bp_origins fn bp /\
  (!bid u. u IN pointer_derived_vars fn (ptr_bp_alloc_roots fn bid) ==>
    ?off. MEM (Ptr (Allocation bid) off) (bp_get_ptrs bp u)) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\ bp_get_ptrs bp v = [Ptr (Allocation aid) off] /\
  v IN pointer_derived_vars fn (ptr_frame_site_roots fn A PG site) /\
  (!r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)) ==>
  FLOOKUP A aid = SOME site
Proof
  strip_tac >>
  `?r. r IN ptr_frame_site_roots fn A PG site /\
       v IN pointer_derived_vars fn {r}` by
    metis_tac[ptr_derived_root_witness, ptr_frame_site_roots_finite] >>
  first_x_assum drule >> strip_tac
  >- (`pointer_derived_vars fn {r} SUBSET
         pointer_derived_vars fn (ptr_bp_alloc_roots fn bid)` by
        (irule ptr_derived_mono >> simp[ptr_bp_alloc_roots_finite, SUBSET_DEF]) >>
      `v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn bid)` by
        fs[SUBSET_DEF] >>
      qpat_x_assum `!bid u. _` (qspecl_then [`bid`, `v`] mp_tac) >>
      simp[] >> metis_tac[])
  >> `pointer_derived_vars fn {r} SUBSET
        pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)` by
       (irule ptr_derived_mono >> simp[ptr_roots_finite, SUBSET_DEF]) >>
  `v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)` by
    fs[SUBSET_DEF] >>
  `v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)` by
    (fs[ptr_bp_origins_def] >> metis_tac[]) >>
  `FINITE (alloca_roots fn)` by
    (irule SUBSET_FINITE_I >> qexists `ptr_roots P fn` >>
     simp[ptr_roots_finite, ptr_roots_def, SUBSET_DEF]) >>
  `pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) SUBSET
     pointer_derived_vars fn (alloca_roots fn)` by
    (irule ptr_derived_mono >> simp[ptr_bp_alloc_roots_finite] >>
     simp[SUBSET_DEF, ptr_bp_alloc_roots_def, alloca_roots_def] >> metis_tac[]) >>
  fs[fn_ptr_ok_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_singleton_write_site:
  fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) /\
  ptr_bp_origins fn bp /\
  (!i. MEM i (fn_insts fn) ==> FST (bp_handle_inst bp i) = F) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\ bp_get_ptrs bp v = [Ptr (Allocation aid) off] /\
  v IN pointer_derived_vars fn (ptr_frame_site_roots fn A PG site) /\
  (!r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)) ==>
  FLOOKUP A aid = SOME site
Proof
  strip_tac >> irule ptr_covered_singleton_write_site >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[ptr_bp_stable_coverage]
QED

Theorem ptr_supported_singleton_write_site:
  fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) /\
  ptr_bp_origins fn bp /\
  (!i. MEM i (fn_insts fn) ==> FST (bp_handle_inst bp i) = F) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\ bp_get_ptrs bp v = [Ptr (Allocation aid) off] /\
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site /\
  FLOOKUP G v = SOME site /\
  (!r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)) ==>
  FLOOKUP A aid = SOME site
Proof
  strip_tac >> irule ptr_singleton_write_site >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[ptr_site_supported_def] >> metis_tac[]
QED

Theorem ptr_production_singleton_write_site:
  fn_ptr_ok P fn /\ wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\
  bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v =
    [Ptr (Allocation aid) off] /\
  v IN pointer_derived_vars fn (ptr_frame_site_roots fn A PG site) /\
  (!r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)) ==>
  FLOOKUP A aid = SOME site
Proof
  strip_tac >>
  `!bid u. u IN pointer_derived_vars fn (ptr_bp_alloc_roots fn bid) ==>
    ?off. MEM (Ptr (Allocation bid) off)
      (bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) u)` by
    (rpt strip_tac >> irule ptr_bp_production_coverage >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[bp_scan_production_complete]) >>
  irule ptr_covered_singleton_write_site >> metis_tac[]
QED

Theorem ptr_supported_production_singleton_write_site:
  fn_ptr_ok P fn /\ wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\
  bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v =
    [Ptr (Allocation aid) off] /\
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site /\
  FLOOKUP G v = SOME site /\
  (!r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)) ==>
  FLOOKUP A aid = SOME site
Proof
  strip_tac >> irule ptr_production_singleton_write_site >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[ptr_site_supported_def] >> metis_tac[]
QED
