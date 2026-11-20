Theory fnFrameSymbolicReady
Ancestors
  fnFrameSymbolicPrefix fnFramePrefixEntry fnFramePrefixDriver
  fnFramePrefix asmSplice asmSem frameJointTrace list arithmetic
  codegenSymRel asmSymRelocLabelsOwn asmSpliceOwn

Theorem normal_frame_symbolic_plan_active_own:
  normal_frame_symbolic_plan_own allow_own lo env own rpolicy unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs h) a ss /\
  code_labels_agree prog lo /\ focus_s7_symbolic_context_own allow_own unit prog /\
  active_inst fn inst s /\ ~is_param_opcode inst.inst_opcode ==>
  ?m ready rss ra rest mem0 ret srest labs0.
    asm_steps lo (build_offset_to_pc prog) prog m a = AsmOK ready /\
    sym_steps_mode allow_own prog env own m ss = SymOK rss /\
    active_frame_symbolic_plan_own lo env own rpolicy unit cpl prog fn s ready
      ra rest mem0 ret srest labs0 rss
Proof
  strip_tac >>
  qhdtm_x_assum `normal_frame_symbolic_plan_own`
    (strip_assume_tac o REWRITE_RULE [normal_frame_symbolic_plan_own_def])
  >- (qexistsl_tac [`0`, `a`, `ss`, `ra`, `rest`, `mem0`, `ret`, `srest`, `labs0`] >>
      Cases_on `allow_own` >>
      simp[asm_steps_def, sym_steps_mode_def, asmSpliceTheory.sym_steps_def,
           sym_steps_own_def]) >>
  `entry_frame_plan_reloc lo rpolicy unit cpl prog fn entry s a ra pc_ret rest mem0` by
    fs[entry_frame_symbolic_plan_own_def] >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (`s.vs_inst_idx <= LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
       fs[entry_frame_plan_reloc_def] >>
     Cases_on `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`
     >- (drule_all entry_frame_active_param_reloc >> simp[]) >>
     decide_tac) >>
  drule_all entry_frame_symbolic_plan_ready_own >>
  disch_then (qx_choosel_then [`m`, `ready`, `rss`] strip_assume_tac) >>
  qexistsl_tac [`m`, `ready`, `rss`, `ra`, `rest`, `mem0`, `ret`, `srest`, `labs0`] >>
  simp[]
QED
