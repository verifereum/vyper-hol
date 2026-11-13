Theory fnLineageInvEdgeFacts
Ancestors cfgCorrectnessProof stackPlanGen cfgAnalysisProps venomExecProps cfgTransform venomInst venomWf list rich_list

Theorem ready_outgoing_block_nonhalting:
  !fn pred bb succ.
    codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME bb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) pred) ==>
    ~bb_is_halting bb
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = pred` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all cfg_analyze_preserves_bb_succs >> strip_tac >>
  spose_not_then assume_tac >>
  `bb.bb_instructions <> [] /\
   is_halting_opcode (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_is_halting_def] >>
  `codegen_ready_inst (LAST bb.bb_instructions)` by
    (fs[codegen_ready_fn_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  gvs[] >>
  qpat_x_assum `MEM succ _` mp_tac >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >- gvs[] >>
  gvs[] >>
  Cases_on `(LAST (h::t)).inst_opcode` >>
  gvs[is_halting_opcode_def, codegen_ready_inst_def,
      is_terminator_def, get_successors_def] >>
  simp[MEM_MAP, MEM_FILTER, EVERY_MEM] >>
  fs[EVERY_MEM] >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem ready_incoming_nonentry:
  !fn pred lbl.
    codegen_ready_fn fn /\ MEM lbl (cfg_succs_of (cfg_analyze fn) pred) ==>
    fn_entry_label fn <> SOME lbl
Proof
  rpt gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[cfg_edge_symmetry_uncond] >>
  gvs[fn_entry_label_def, AllCaseEqs()] >>
  gvs[codegen_ready_fn_def, block_entries_ready_def, NULL_EQ]
QED

Theorem ready_outgoing_terminal_shape:
  !fn lbl bb succ.
    codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    ~bb_is_halting bb /\
    (LAST bb.bb_instructions).inst_opcode <> NOP /\
    (LAST bb.bb_instructions).inst_opcode <> OFFSET /\
    (LAST bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (LAST bb.bb_instructions).inst_opcode
Proof
  rpt gen_tac >> strip_tac >>
  `~bb_is_halting bb` by metis_tac[ready_outgoing_block_nonhalting] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[codegen_ready_fn_def, wf_function_def] >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
  gvs[is_terminator_def, is_param_opcode_def]
QED
