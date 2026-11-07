Theory fnLineageInvJmpEnvelope
Ancestors fnLineageInvControl fnLineageInvTerminal fnLineageInvActualReplay
  fnPlanLineageLiveness stackPlanGen venomWf venomExecProps codegenReadyCompute
  list rich_list pred_set

Theorem analyzed_jmp_target_end_live:
  !fn bb k targets.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_opcode = JMP /\
    join_target_ops (liveness_analyze fn) fn bb.bb_label
      (EL k bb.bb_instructions) = SOME targets ==>
    set targets = set (MAP Var
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))
Proof
  rpt gen_tac >> strip_tac >>
  `SUC k = LENGTH bb.bb_instructions` by metis_tac[analyzed_jmp_terminal_index] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `LAST bb.bb_instructions = EL k bb.bb_instructions` by
    (`k = PRE (LENGTH bb.bb_instructions)` by decide_tac >> simp[LAST_EL]) >>
  gvs[join_target_ops_def, AllCaseEqs()] >>
  drule_all analyzed_live_out_jmp >> strip_tac >>
  gvs[EXTENSION, MEM_MAP] >> metis_tac[]
QED
