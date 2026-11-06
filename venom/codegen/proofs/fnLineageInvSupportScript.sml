Theory fnLineageInvSupport
Ancestors
  fnPlanLineageCallers livenessProofs cfgAnalysisProps venomWf
  stackPlanGen asmIR venomInst passSharedDefs codegenReadyCompute list pred_set

Theorem inst_uses_compute_operands_nonlog:
  !inst v. inst.inst_opcode <> LOG /\ MEM v (inst_uses inst) ==>
    MEM (Var v) (compute_operands inst)
Proof
  rpt gen_tac >>
  simp[compute_operands_def, inst_uses_def, MEM_operand_vars_eq_Var] >>
  IF_CASES_TAC
  >- simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER] >>
  simp[]
QED

Theorem analyzed_nonlog_live_upper_support:
  !fn bb i.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> LOG ==>
    set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label i)) SUBSET
    set (MAP Var (venomInst$operand_vars (stackPlanGen$compute_operands (EL i bb.bb_instructions)) ++
      live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label i =
    liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >> simp[]) >>
  simp[SUBSET_DEF, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  gvs[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
      MEM_FILTER, MEM_APPEND] >>
  drule_all inst_uses_compute_operands_nonlog >>
  rewrite_tac[GSYM MEM_operand_vars_eq_Var] >>
  strip_tac >> metis_tac[]
QED
