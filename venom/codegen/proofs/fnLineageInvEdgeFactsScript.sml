Theory fnLineageInvEdgeFacts
Ancestors stackPlanGen cfgAnalysisProps venomExecProps cfgTransform venomInst list rich_list

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
