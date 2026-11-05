Theory concretizePtrProductionCoverage
Ancestors concretizeAnalysisOriginCoverage concretizeAnalysisOriginFlow
  concretizeAnalysisBaseModel concretizeAnalysisAffine concretizeAnalysisRoots
  concretizePtrClosure concretizePtrBPOrigins pointerClosure pointerConfinedDefs
  ptrDiscipline venomWf venomInst basePtrDefs list pred_set removeUnusedSsaProofs

Theorem ptr_flow_step_descriptor[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var u) inst.inst_operands /\ u IN fn_pv P fn /\
  MEM out inst.inst_outputs ==>
  ?seed sources. bp_descriptor inst = SOME (out,seed,sources) /\ u IN sources
Proof
  strip_tac >>
  `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
   inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI` by
    (Cases_on `inst.inst_opcode` >> fs[is_pointer_preserving_op_def]) >>
  `inst_output inst = SOME out` by
    (gvs[inst_wf_def, inst_output_def, AllCaseEqs()] >>
     Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  gvs[inst_wf_def]
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      `!l. ~MEM (Label l) inst.inst_operands` by
        (fs[fn_ptr_ok_def] >>
         qpat_x_assum `!i. MEM i (fn_insts fn) ==> _`
           (qspec_then `inst` mp_tac) >> simp[] >> metis_tac[]) >>
      Cases_on `h` >> gvs[bp_descriptor_def])
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      `!l. ~MEM (Label l) inst.inst_operands` by
        (fs[fn_ptr_ok_def] >>
         qpat_x_assum `!i. MEM i (fn_insts fn) ==> _`
           (qspec_then `inst` mp_tac) >> simp[] >> metis_tac[]) >>
      Cases_on `h` >> gvs[bp_descriptor_def] >>
      gvs[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def,
          fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[])
  >- (Cases_on `inst.inst_operands` >> gvs[bp_descriptor_def])
  >> simp[bp_descriptor_def] >>
  disj2_tac >>
  `!ops. phi_well_formed ops /\ MEM (Var u) ops ==>
     MEM u (MAP SND (phi_pairs ops))` suffices_by metis_tac[] >>
  ho_match_mp_tac phi_pairs_ind >>
  simp[phi_well_formed_def, phi_pairs_def] >> rpt strip_tac >> gvs[]
QED

Theorem ptr_bp_derived_flow:
  fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) /\
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  bp_flow fn aid v
Proof
  strip_tac >>
  `pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) SUBSET
     {u | u IN fn_pv P fn /\ bp_flow fn aid u}` suffices_by
    simp[SUBSET_DEF] >>
  irule ptr_derived_least >> simp[ptr_bp_alloc_roots_finite] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (simp[fn_pv_def] >> irule pointer_derived_vars_closed >>
          simp[ptr_roots_finite] >> goal_assum (drule_at Any) >>
          gvs[fn_pv_def] >> metis_tac[])
      >> `inst_wf inst` by fs[EVERY_MEM] >>
      drule_all ptr_flow_step_descriptor >> strip_tac >>
      irule bp_flow_descriptor >> metis_tac[])
  >> simp[SUBSET_DEF, ptr_bp_alloc_roots_def] >> rpt strip_tac
  >- (simp[fn_pv_def] >>
      `x IN ptr_roots P fn` by
        (simp[ptr_roots_def, alloca_roots_def] >> metis_tac[]) >>
      metis_tac[pointer_derived_vars_roots, ptr_roots_finite, SUBSET_DEF])
  >> metis_tac[bp_flow_seed]
QED

Theorem ptr_bp_production_coverage:
  fn_ptr_ok P fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
  (!i. MEM i (fn_insts fn) ==> MEM i (bp_scan_insts fn cfg.cfg_dfs_pre)) /\
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  ?off. MEM (Ptr (Allocation aid) off)
    (bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) cfg fn) v)
Proof
  strip_tac >> drule_all ptr_bp_derived_flow >> strip_tac >>
  drule_all bp_flow_production_coverage >>
  simp[concretizeAnalysisBoundaryTheory.bp_bases_def, MEM_MAP] >>
  strip_tac >> Cases_on `y` >> gvs[ptr_base_def] >> metis_tac[]
QED
