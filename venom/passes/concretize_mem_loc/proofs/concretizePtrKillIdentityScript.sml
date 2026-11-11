Theory concretizePtrKillIdentity
Ancestors
  concretizePtrRuntimeTotality concretizePtrActivationSupport
  concretizePtrRootCover concretizePtrSingletonSite concretizePtrKillProbe
  concretizePtrProductionCoverage concretizeAnalysisScanCoverage
  concretizePtrBPOrigins concretizePtrClosure concretizePtrFrameOrigins
  concretizePtrRuntimeOrigins
  concretizeMemLocDefs concretizeAnalysisRoots pointerConfinedDefs pointerClosure
  ptrDiscipline o1PassContract venomWf cfgWf cfgAnalysisProps basePtrDefs
  venomExecSemantics venomState venomInst memLocDefs finite_map pred_set list enumeral

Theorem ptr_find_base_member:
  MEM a (find_base_allocas bp (Var v)) <=>
  ?off. MEM (Ptr a off) (bp_get_ptrs bp v)
Proof
  `!xs. set (incr_ssort alloc_to xs) = set xs` by
    metis_tac[set_OWL_thm, OWL] >>
  simp[find_base_allocas_def, MEM_MAP] >>
  eq_tac >> rpt strip_tac
  >- (Cases_on `p` >> gvs[] >> metis_tac[]) >>
  qexists `Ptr a off` >> simp[]
QED

Theorem ptr_base_write_pure_local:
  fn_ptr_ok P fn /\ ptr_bp_origins fn bp /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\ find_base_allocas bp (Var v) = [Allocation aid] ==>
  v IN (pointer_derived_vars fn (alloca_roots fn) DIFF
        pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn))
Proof
  strip_tac >>
  `?off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v)` by
    metis_tac[ptr_find_base_member, MEM] >>
  `v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)` by
    metis_tac[ptr_bp_origins_def] >>
  `FINITE (alloca_roots fn)` by
    (irule SUBSET_FINITE_I >> qexists `ptr_roots P fn` >>
     simp[ptr_roots_finite, ptr_roots_def, SUBSET_DEF]) >>
  `pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) SUBSET
    pointer_derived_vars fn (alloca_roots fn)` by
    (irule ptr_derived_mono >> simp[ptr_bp_alloc_roots_finite] >>
     simp[SUBSET_DEF, ptr_bp_alloc_roots_def, alloca_roots_def] >> metis_tac[]) >>
  fs[fn_ptr_ok_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_covered_base_write_site:
  fn_ptr_ok P fn /\ ptr_bp_origins fn bp /\
  (!bid u. u IN pointer_derived_vars fn (ptr_bp_alloc_roots fn bid) ==>
    ?off. MEM (Ptr (Allocation bid) off) (bp_get_ptrs bp u)) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\ find_base_allocas bp (Var v) = [Allocation aid] /\
  v IN pointer_derived_vars fn (ptr_frame_site_roots fn A PG site) /\
  (!r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)) ==>
  FLOOKUP A aid = SOME site
Proof
  strip_tac >>
  `v IN (pointer_derived_vars fn (alloca_roots fn) DIFF
         pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn))` by
    metis_tac[ptr_base_write_pure_local] >>
  `?r. r IN ptr_frame_site_roots fn A PG site /\
       v IN pointer_derived_vars fn {r}` by
    metis_tac[ptr_derived_root_witness, ptr_frame_site_roots_finite] >>
  qpat_x_assum `!r. _` drule >> strip_tac
  >- (`pointer_derived_vars fn {r} SUBSET
         pointer_derived_vars fn (ptr_bp_alloc_roots fn bid)` by
        (irule ptr_derived_mono >> simp[ptr_bp_alloc_roots_finite, SUBSET_DEF]) >>
      `v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn bid)` by
        fs[SUBSET_DEF] >>
      `?off. MEM (Ptr (Allocation bid) off) (bp_get_ptrs bp v)` by metis_tac[] >>
      `MEM (Allocation bid) (find_base_allocas bp (Var v))` by
        metis_tac[ptr_find_base_member] >> gvs[]) >>
  `pointer_derived_vars fn {r} SUBSET
     pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)` by
    (irule ptr_derived_mono >> simp[ptr_roots_finite, SUBSET_DEF]) >>
  fs[SUBSET_DEF]
QED

Theorem ptr_reachable_base_write_identity:
  frame_reachable vs ctx stk PG G tn fn inst s /\ o1_run_state_ok vs /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY ssa_form ctx.ctx_functions /\
  EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  wf_function fn /\ all_reachable fn /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  find_base_allocas (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (Var v) = [Allocation aid] /\ lookup_var v s = SOME w ==>
  ?site. FLOOKUP G v = SOME site /\ FLOOKUP s.vs_allocas aid = SOME site
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions` by
    metis_tac[concretizePtrParamSupportTheory.ptr_frame_current_static] >>
  `fn_ptr_ok P fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `v IN (pointer_derived_vars fn (alloca_roots fn) DIFF
         pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn))` by
    metis_tac[ptr_base_write_pure_local] >>
  `?site. FLOOKUP G v = SOME site` by
    metis_tac[ptr_reachable_pure_local_totality] >>
  qexists `site` >> simp[] >>
  `ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site` by
    metis_tac[ptr_frame_current_table_support] >>
  `!bid u. u IN pointer_derived_vars fn (ptr_bp_alloc_roots fn bid) ==>
    ?off. MEM (Ptr (Allocation bid) off)
      (bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) u)` by
    (rpt strip_tac >> irule ptr_bp_production_coverage >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[bp_scan_production_complete]) >>
  `!r. r IN ptr_frame_site_roots fn s.vs_allocas PG site ==>
    (?bid. FLOOKUP s.vs_allocas bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)` by
    metis_tac[ptr_frame_current_root_cover] >>
  irule ptr_covered_base_write_site >>
  fs[ptr_site_supported_def] >> metis_tac[]
QED

Theorem evaluated_member[local]:
  !operands vals. eval_operands operands s = SOME vals ==>
  !op. MEM op operands ==> ?w. eval_operand op s = SOME w
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ptr_reachable_successful_kill_identity:
  frame_reachable vs ctx stk PG G tn fn inst s /\ o1_run_state_ok vs /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY ssa_form ctx.ctx_functions /\
  EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  wf_function fn /\ all_reachable fn /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  MEM inst (fn_insts fn) /\
  ptr_ml_can_kill (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) sizes inst /\
  step_inst fuel ctx inst s = OK s' ==>
  ?ops v w site. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    lookup_var v s = SOME w /\ FLOOKUP G v = SOME site /\
    FLOOKUP s.vs_allocas aid = SOME site
Proof
  strip_tac >> drule ptr_kill_has_variable_write_operand >> strip_tac >>
  `?vals. eval_operands inst.inst_operands s = SOME vals` by
    metis_tac[ptr_successful_kill_operands_ready] >>
  `MEM (Var v) inst.inst_operands` by
    (irule concretizePtrRuntimeGenerationTheory.ptr_write_op_operand >>
     simp[inst_write_op_def]) >>
  `?w. lookup_var v s = SOME w` by
    metis_tac[evaluated_member, eval_operand_def] >>
  drule_all ptr_reachable_base_write_identity >> strip_tac >>
  metis_tac[]
QED

(* This boundary establishes allocation identity, not production size
   accuracy, the non-revert guard on access_ok, or universal no-kill coverage. *)
