Theory fnBlockPlanStaticRetRegion
Ancestors
  stackPlanGen cfgAnalysisProps venomExecProps simplifyCfgStruct
  venomWf venomInst cfgTransform cfgDefs relation

Theorem ready_block_ret_last:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = RET ==>
  LAST bb.bb_instructions = inst
Proof
  strip_tac >> drule lookup_block_MEM >> strip_tac >>
  `bb_well_formed bb` by
    (fs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  irule EQ_SYM >> irule bb_well_formed_terminator_last >>
  simp[is_terminator_def] >> metis_tac[]
QED

Theorem ready_block_ret_not_halting:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = RET ==>
  ~bb_is_halting bb
Proof
  strip_tac >> drule_all ready_block_ret_last >>
  simp[bb_is_halting_def, is_halting_opcode_def]
QED

Theorem ready_terminal_successors_empty[local]:
  codegen_ready_inst inst /\ is_terminator inst.inst_opcode /\
  inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
  inst.inst_opcode <> DJMP ==>
  get_successors inst = []
Proof
  simp[codegen_ready_inst_def, get_successors_def] >> strip_tac >>
  `FILTER IS_SOME (MAP get_label inst.inst_operands) = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MAP,
          listTheory.EVERY_MEM] >>
     fs[listTheory.EVERY_MEM]) >> simp[]
QED

Theorem ready_block_ret_successors_empty:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = RET ==>
  cfg_succs_of (cfg_analyze fn) lbl = []
Proof
  strip_tac >> drule_all ready_block_ret_last >> strip_tac >>
  drule lookup_block_MEM >> strip_tac >>
  drule lookup_block_label >> strip_tac >>
  `codegen_ready_inst inst` by
    (fs[codegen_ready_fn_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `get_successors inst = []` by
    (irule ready_terminal_successors_empty >> simp[is_terminator_def]) >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all cfg_analyze_preserves_bb_succs >>
  Cases_on `bb.bb_instructions` >> simp[bb_succs_def] >> gvs[]
QED

Theorem ready_halting_successors_empty:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  bb_is_halting bb ==>
  cfg_succs_of (cfg_analyze fn) lbl = []
Proof
  strip_tac >> drule lookup_block_MEM >> strip_tac >>
  drule lookup_block_label >> strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_is_halting_def] >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
    (rewrite_tac[listTheory.MEM_EL] >>
     qexists_tac `PRE (LENGTH bb.bb_instructions)` >>
     simp[listTheory.LAST_EL] >>
     Cases_on `bb.bb_instructions` >> gvs[]) >>
  `codegen_ready_inst (LAST bb.bb_instructions)` by
    (fs[codegen_ready_fn_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `get_successors (LAST bb.bb_instructions) = []` by
    (irule ready_terminal_successors_empty >>
     fs[bb_is_halting_def] >>
     Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     gvs[is_halting_opcode_def, is_terminator_def]) >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all cfg_analyze_preserves_bb_succs >>
  Cases_on `bb.bb_instructions` >> simp[bb_succs_def] >> gvs[]
QED

(* Reuse cfg_path, the existing finite successor reachability relation. *)
Theorem cfg_path_first_step:
  cfg_path cfg l t ==>
  l = t \/ ?s. MEM s (cfg_succs_of cfg l) /\ cfg_path cfg s t
Proof
  simp[cfg_path_def, Once RTC_CASES1]
QED

Theorem cfg_path_predecessor_closed:
  MEM s (cfg_succs_of cfg l) /\ cfg_path cfg s t ==>
  cfg_path cfg l t
Proof
  strip_tac >> rewrite_tac[cfg_path_def] >>
  once_rewrite_tac[RTC_CASES1] >>
  disj2_tac >> qexists_tac `s` >> fs[cfg_path_def]
QED

Theorem cfg_path_successor_free:
  cfg_succs_of cfg l = [] /\ cfg_path cfg l t ==> l = t
Proof
  strip_tac >> drule cfg_path_first_step >> simp[]
QED
