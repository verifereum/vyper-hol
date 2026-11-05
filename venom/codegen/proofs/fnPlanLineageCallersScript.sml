Theory fnPlanLineageCallers
Ancestors
  fnPlanLineageSetup fnPlanLineageDemand fnPlanLineagePath
  livenessProofs cfgAnalysisProps venomWf stackPlanGen asmIR codegenReadyCompute
  passSharedDefs venomInst list rich_list

Theorem compute_operands_inst_uses:
  !inst v. MEM (Var v) (compute_operands inst) ==> MEM v (inst_uses inst)
Proof
  rpt gen_tac >>
  simp[compute_operands_def, inst_uses_def, MEM_operand_vars_eq_Var] >>
  IF_CASES_TAC
  >- simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER] >>
  IF_CASES_TAC
  >- (Cases_on `inst.inst_operands` >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem analyzed_computed_operand_demand:
  !fn bb i v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
     (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
      ~MEM v (EL i bb.bb_instructions).inst_outputs)) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)
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
  gvs[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
      MEM_FILTER, MEM_APPEND, venomInstTheory.inst_defs_def] >>
  metis_tac[compute_operands_inst_uses, livenessDefsTheory.MEM_ordered_inst_uses]
QED
