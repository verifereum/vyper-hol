Theory fnLineageInvControl
Ancestors fnLineageInvSupport cfgTransform cfgAnalysisProps venomWf
  stackPlanGen venomInst venomExecProps asmIR list rich_list

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
