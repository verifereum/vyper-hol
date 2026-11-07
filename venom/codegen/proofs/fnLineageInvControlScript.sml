Theory fnLineageInvControl
Ancestors fnLineageInvSupport cfgTransform cfgAnalysisProps venomWf
  stackPlanGen venomInst venomExecProps asmIR list rich_list
  fnLineageInvLivenessDistinct fnPlanLineageLiveness

Theorem analyzed_successor_nonhalting:
 !fn lbl bb succ.
 codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
 MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==> ~bb_is_halting bb
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn /\ fn_inst_wf fn` by gvs[codegen_ready_fn_def] >>
 `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
   metis_tac[lookup_block_MEM, lookup_block_label] >>
 drule_all cfg_analyze_preserves_bb_succs >> strip_tac >>
 `bb.bb_instructions <> []` by metis_tac[wf_function_def, bb_well_formed_def] >>
 `inst_wf (LAST bb.bb_instructions)` by
   (gvs[fn_inst_wf_def] >> metis_tac[LAST_MEM]) >>
 `codegen_ready_inst (LAST bb.bb_instructions)` by
   (gvs[codegen_ready_fn_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
 spose_not_then assume_tac >>
 `EVERY (\op. get_label op = NONE) (LAST bb.bb_instructions).inst_operands` by
   (gvs[bb_is_halting_def] >>
    Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
    gvs[is_halting_opcode_def, codegen_ready_inst_def, is_terminator_def]) >>
 `FILTER IS_SOME (MAP get_label (LAST bb.bb_instructions).inst_operands) = []` by
   (gvs[FILTER_EQ_NIL, EVERY_MAP, EVERY_MEM]) >>
 Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, get_successors_def]
QED

Theorem analyzed_jmp_terminal_index:
 !fn bb k.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
 (EL k bb.bb_instructions).inst_opcode = JMP ==>
 SUC k = LENGTH bb.bb_instructions
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `bb_well_formed bb` by metis_tac[wf_function_def] >>
 `k = PRE (LENGTH bb.bb_instructions)` by
   (gvs[bb_well_formed_def] >> first_x_assum irule >> simp[is_terminator_def]) >>
 decide_tac
QED

Theorem analyzed_jmp_target_footprint:
 !fn bb k targets.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_opcode = JMP /\
 join_target_ops (liveness_analyze fn) fn bb.bb_label
   (EL k bb.bb_instructions) = SOME targets ==>
 ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
 set targets SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k))
Proof
 rpt gen_tac >> strip_tac >>
 `SUC k = LENGTH bb.bb_instructions` by metis_tac[analyzed_jmp_terminal_index] >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
   (irule venomExecPropsTheory.MEM_lookup_block >>
    gvs[wf_function_def, fn_labels_def]) >>
 `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
   metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze] >>
 `LAST bb.bb_instructions = EL k bb.bb_instructions` by
   (`bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
    `k = PRE (LENGTH bb.bb_instructions)` by decide_tac >> simp[LAST_EL]) >>
 gvs[join_target_ops_def, AllCaseEqs()] >>
 conj_tac
 >- (irule ALL_DISTINCT_MAP_INJ >> simp[] >>
     `MEM target_bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     `phi_block_ready (liveness_analyze fn) target_bb` by
       metis_tac[fnPlanPrefixTheory.phi_codegen_block_ready] >>
     irule fnPlanLineagePhiMapsTheory.input_vars_from_distinct >>
     gvs[phi_block_ready_def, analyzed_live_vars_distinct]) >>
 conj_tac >- simp[EVERY_MAP, EVERY_MEM, stackPlanTypesTheory.is_var_operand_def] >>
 `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
 drule_all analyzed_live_out_jmp >> strip_tac >>
 `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
   (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
    metis_tac[]) >>
 `live_vars_at (liveness_analyze fn) bb.bb_label k =
   liveness_transfer fn.fn_blocks (EL k bb.bb_instructions)
     (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))` by
   (drule livenessAnalysisPropsTheory.live_vars_at_transfer >>
    disch_then (qspecl_then [`bb.bb_label`, `bb`, `k`] mp_tac) >> simp[]) >>
 `inst_defs (EL k bb.bb_instructions) = []` by
   (gvs[fn_inst_wf_def, codegen_ready_fn_def] >>
    `inst_wf (EL k bb.bb_instructions)` by
      (first_x_assum irule >> qexists_tac `bb` >> simp[] >>
       irule EL_MEM >> decide_tac) >>
    gvs[inst_wf_def, inst_defs_def]) >>
 gvs[pred_setTheory.SUBSET_DEF, MEM_MAP, livenessDefsTheory.liveness_transfer_def,
     livenessProofsTheory.live_update_mem, pred_setTheory.EXTENSION] >>
 metis_tac[]
QED
