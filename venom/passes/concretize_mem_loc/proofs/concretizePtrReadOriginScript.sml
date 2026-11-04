Theory concretizePtrReadOrigin
Ancestors
  concretizePtrChronologicalDemand concretizePtrSelectedOrigin
  concretizePtrCallAncestry concretizePtrActivationSupport
  concretizePtrProductionCoverage concretizePtrRuntimeGeneration
  concretizeAnalysisScanCoverage concretizeAnalysisLivenessTransfer
  concretizeAnalysisBoundary concretizeAnalysisWriteSafety
  concretizeMemLocDefs basePtrDefs
  ptrDiscipline pointerConfinedDefs venomWf venomInst
  list pred_set finite_map

Theorem ptr_read_op_operand:
  inst_read_op inst = SOME op ==> MEM op inst.inst_operands
Proof
  simp[inst_read_op_def, memLocDefsTheory.mem_read_ops_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_REVERSE, MEM]
QED

Theorem ptr_production_selected_read_seed:
  fn_ptr_ok P fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
  wf_function fn /\ all_reachable fn /\ MEM inst (fn_insts fn) /\
  MEM (Var v) inst.inst_operands /\
  (inst_read_op inst = SOME (Var v) \/ inst.inst_opcode = INVOKE) /\
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  ml_read_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems inst
Proof
  strip_tac >>
  `?off. MEM (Ptr (Allocation aid) off)
    (bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v)` by
    (irule ptr_bp_production_coverage >> simp[] >>
     metis_tac[bp_scan_production_complete]) >>
  `MEM (Allocation aid)
    (find_base_allocas (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) (Var v))` by
    (simp[GSYM bp_bases_find_base_allocas, bp_bases_def, MEM_MAP] >>
     metis_tac[ptr_base_def]) >>
  simp[ml_read_gen_def, find_base_allocas_opt_def] >>
  `inst_wf inst` by fs[EVERY_MEM] >>
  gvs[inst_wf_def, ml_operand_gen_def] >> metis_tac[]
QED

Definition ptr_activation_read_seed_def:
  ptr_activation_read_seed mems site f <=>
    ?aid. FLOOKUP f.cf_state.vs_allocas aid = SOME site /\
      ml_read_gen (Allocation aid)
        (bp_analyze_fuel (concretize_memloc_fuel f.cf_fn)
          (cfg_analyze f.cf_fn) f.cf_fn) mems f.cf_inst
End

Theorem ptr_activation_selected_read_seed:
  ptr_activation_ready P site f /\
  MEM (Var v) f.cf_inst.inst_operands /\
  (inst_read_op f.cf_inst = SOME (Var v) \/ f.cf_inst.inst_opcode = INVOKE) /\
  FLOOKUP f.cf_prov v = SOME site ==>
  ptr_activation_read_seed mems site f \/ MEM (SOME site) f.cf_params
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ptr_activation_ready P site f` mp_tac >>
  simp[ptr_activation_ready_def] >> strip_tac >>
  drule_all ptr_selected_origin >> strip_tac
  >- (disj1_tac >> simp[ptr_activation_read_seed_def] >>
      qexists `aid` >> simp[] >>
      irule ptr_production_selected_read_seed >> simp[] >> metis_tac[]) >>
  disj2_tac >> simp[MEM_EL] >> qexists `w2n idx` >> simp[]
QED

Theorem ptr_ancestry_selected_read_seed:
  !stk f v.
  ptr_call_ancestry f.cf_params stk /\ ptr_activation_ready P site f /\
  EVERY (ptr_activation_ready P site) stk /\
  MEM (Var v) f.cf_inst.inst_operands /\
  (inst_read_op f.cf_inst = SOME (Var v) \/ f.cf_inst.inst_opcode = INVOKE) /\
  FLOOKUP f.cf_prov v = SOME site ==>
  ptr_activation_read_seed mems site f \/
  ?n w. n < LENGTH stk /\
    MEM (Var w) (EL n stk).cf_inst.inst_operands /\
    FLOOKUP (EL n stk).cf_prov w = SOME site /\
    ptr_activation_read_seed mems site (EL n stk)
Proof
  Induct >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)
  >- (drule_all ptr_activation_selected_read_seed >>
      gvs[ptr_call_ancestry_def]) >>
  drule_all ptr_activation_selected_read_seed >>
  disch_then (qspec_then `mems` strip_assume_tac) >- simp[] >>
  `?w. MEM (Var w) h.cf_inst.inst_operands /\ FLOOKUP h.cf_prov w = SOME site` by
    metis_tac[ptr_call_ancestry_import] >>
  `ptr_call_ancestry h.cf_params stk /\ h.cf_inst.inst_opcode = INVOKE` by
    fs[ptr_call_ancestry_def] >>
  qpat_x_assum `EVERY _ (h::stk)` mp_tac >>
  simp[listTheory.EVERY_DEF] >> strip_tac >>
  first_x_assum (qspecl_then [`h`,`w`] mp_tac) >> simp[] >> strip_tac
  >- (disj2_tac >> qexistsl [`0`,`w`] >> simp[]) >>
  disj2_tac >> qexistsl [`SUC n`,`w'`] >> simp[]
QED

Theorem ptr_frame_selected_read_seed:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\
  EVERY all_reachable ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  MEM (Var v) inst.inst_operands /\ FLOOKUP G v = SOME site /\
  (inst_read_op inst = SOME (Var v) \/ inst.inst_opcode = INVOKE) ==>
  (?aid. FLOOKUP s.vs_allocas aid = SOME site /\
    ml_read_gen (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems inst) \/
  (?n aid w. n < LENGTH stk /\
    FLOOKUP (EL n stk).cf_state.vs_allocas aid = SOME site /\
    MEM (Var w) (EL n stk).cf_inst.inst_operands /\
    FLOOKUP (EL n stk).cf_prov w = SOME site /\
    ml_read_gen (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel (EL n stk).cf_fn)
        (cfg_analyze (EL n stk).cf_fn) (EL n stk).cf_fn) mems (EL n stk).cf_inst)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_frame_table_support_invariant >> strip_tac >>
  drule ptr_frame_operand_instructions >> strip_tac >>
  drule ptr_frame_call_ancestry >> strip_tac >>
  qspecl_then [`stk`, `<| cf_fn := fn; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>`, `v`]
    mp_tac ptr_ancestry_selected_read_seed >>
  simp[ptr_activation_ready_def, ptr_activation_read_seed_def] >>
  (impl_tac >- (gvs[EVERY_MEM, ptr_activation_ready_def] >> metis_tac[])) >>
  metis_tac[]
QED
