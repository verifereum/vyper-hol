Theory fnBlockPlanStaticRetRegion
Ancestors
  stackPlanGen cfgAnalysisProps venomExecProps simplifyCfgStruct
  venomWf venomInst cfgTransform cfgDefs relation
  livenessConvergenceProofs livenessBlockProofs livenessDefs list pred_set

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

Theorem ready_halting_not_ret_reaching:
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME retbb /\
  MEM inst retbb.bb_instructions /\ inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb_is_halting bb ==>
  ~cfg_path (cfg_analyze fn) lbl target
Proof
  strip_tac >> strip_tac >>
  `cfg_succs_of (cfg_analyze fn) lbl = []` by
    (irule ready_halting_successors_empty >> metis_tac[]) >>
  drule_all cfg_path_successor_free >> strip_tac >> gvs[] >>
  drule_all ready_block_ret_not_halting >> simp[]
QED

Theorem must_halt_step_avoids_ret:
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME retbb /\
  MEM inst retbb.bb_instructions /\ inst.inst_opcode = RET /\
  EVERY (\l. ~cfg_path (cfg_analyze fn) l target) labels ==>
  EVERY (\l. ~cfg_path (cfg_analyze fn) l target)
    (must_halt_step (cfg_analyze fn) fn labels lbl)
Proof
  strip_tac >> rewrite_tac[must_halt_step_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  IF_CASES_TAC >-
    (IF_CASES_TAC >> simp[listTheory.EVERY_SNOC] >>
     strip_tac >>
     drule cfg_path_first_step >> strip_tac >-
       (gvs[] >>
        `~bb_is_halting bb` by
          (irule ready_block_ret_not_halting >> metis_tac[]) >>
        `cfg_succs_of (cfg_analyze fn) lbl = []` by
          (irule ready_block_ret_successors_empty >> metis_tac[]) >>
        fs[]) >>
     Cases_on `bb_is_halting bb` >-
       (drule_all ready_halting_not_ret_reaching >> simp[]) >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED

Theorem must_halt_fold_avoids_ret[local]:
  !order labels.
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME retbb /\
  MEM inst retbb.bb_instructions /\ inst.inst_opcode = RET /\
  EVERY (\l. ~cfg_path (cfg_analyze fn) l target) labels ==>
  EVERY (\l. ~cfg_path (cfg_analyze fn) l target)
    (FOLDL (must_halt_step (cfg_analyze fn) fn) labels order)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> irule must_halt_step_avoids_ret >> metis_tac[]
QED

Theorem must_halt_labels_avoids_ret:
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME retbb /\
  MEM inst retbb.bb_instructions /\ inst.inst_opcode = RET ==>
  EVERY (\l. ~cfg_path (cfg_analyze fn) l target)
    (must_halt_labels (cfg_analyze fn) fn)
Proof
  strip_tac >> rewrite_tac[must_halt_labels_def] >>
  irule must_halt_fold_avoids_ret >>
  simp[] >> reverse conj_tac >- (metis_tac[]) >>
  simp[listTheory.EVERY_MAP, listTheory.EVERY_FILTER, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[codegen_ready_fn_def, wf_function_def, fn_labels_def] >>
  metis_tac[MEM_lookup_block, ready_halting_not_ret_reaching]
QED

Theorem ret_reaching_not_must_halt:
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME retbb /\
  MEM inst retbb.bb_instructions /\ inst.inst_opcode = RET /\
  cfg_path (cfg_analyze fn) lbl target ==>
  ~MEM lbl (must_halt_labels (cfg_analyze fn) fn)
Proof
  strip_tac >> drule_all must_halt_labels_avoids_ret >>
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ret_reaching_cleanup_not_safe:
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME retbb /\
  MEM inst retbb.bb_instructions /\ inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  cfg_path (cfg_analyze fn) lbl target ==>
  ~cleanup_height_safe ch growth (cfg_analyze fn) fn bb h /\
  ~cleanup_elision_safe ch growth (cfg_analyze fn) fn bb h
Proof
  strip_tac >> drule_all ret_reaching_not_must_halt >>
  drule lookup_block_label >>
  simp[cleanup_height_safe_def, cleanup_elision_safe_def]
QED

Theorem ready_block_ret_index_last:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = RET ==> k + 1 = LENGTH bb.bb_instructions
Proof
  strip_tac >> drule lookup_block_MEM >> strip_tac >>
  `bb_well_formed bb` by
    (fs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  `is_terminator (EL k bb.bb_instructions).inst_opcode`
    by simp[is_terminator_def] >>
  fs[bb_well_formed_def] >>
  `k = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >> decide_tac
QED

Theorem regional_ret_next_live_empty:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  cfg_reachable_of (cfg_analyze fn) lbl /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = RET ==>
  live_vars_at (liveness_analyze fn) bb.bb_label (k + 1) = []
Proof
  strip_tac >>
  `k + 1 = LENGTH bb.bb_instructions` by
    (irule ready_block_ret_index_last >> metis_tac[]) >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `cfg_succs_of (cfg_analyze fn) lbl = []` by
    (irule ready_block_ret_successors_empty >> metis_tac[]) >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all liveness_recompute_convergence >>
  drule lookup_block_label >>
  simp[liveness_instrs_def, liveness_out_def, same_vars_set,
       live_vars_at_def, liveness_analyze_def] >>
  metis_tac[]
QED

Theorem ready_ret_index_no_jmp:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM ret_inst bb.bb_instructions /\ ret_inst.inst_opcode = RET ==>
  !i. i < LENGTH bb.bb_instructions ==> (EL i bb.bb_instructions).inst_opcode <> JMP
Proof
  strip_tac >> drule_all ready_block_ret_last >> strip_tac >>
  drule lookup_block_MEM >> strip_tac >>
  `bb_well_formed bb` by
    (fs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `EL i bb.bb_instructions = LAST bb.bb_instructions` by
    (irule bb_well_formed_terminator_last >> simp[is_terminator_def, EL_MEM]) >>
  gvs[]
QED
