Theory fnFrameSymbolicReady
Ancestors
  fnFrameSymbolicPrefix fnFramePrefixEntry fnFramePrefixDriver
  fnFramePrefix asmSplice asmSem frameJointTrace list arithmetic

Theorem normal_frame_symbolic_plan_active:
  normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs h) a ss /\
  focus_s7_symbolic_context unit prog /\
  active_inst fn inst s /\ ~is_param_opcode inst.inst_opcode ==>
  ?m ready rss ra rest mem0 ret srest labs0.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog m a = AsmOK ready /\
    sym_steps prog env m ss = SymOK rss /\
    active_frame_symbolic_plan env rpolicy unit cpl prog fn s ready
      ra rest mem0 ret srest labs0 rss
Proof
  strip_tac >>
  qpat_x_assum `normal_frame_symbolic_plan _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [normal_frame_symbolic_plan_def])
  >- (qexistsl_tac [`0`, `a`, `ss`, `ra`, `rest`, `mem0`, `ret`, `srest`, `labs0`] >>
      simp[asm_steps_def, asmSpliceTheory.sym_steps_def]) >>
  `entry_frame_plan rpolicy unit cpl prog fn entry s a ra pc_ret rest mem0` by
    fs[entry_frame_symbolic_plan_def] >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (`s.vs_inst_idx <= LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
       fs[entry_frame_plan_def] >>
     Cases_on `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`
     >- (drule_all entry_frame_active_param >> simp[]) >>
     decide_tac) >>
  drule_all entry_frame_symbolic_plan_ready >>
  disch_then (qx_choosel_then [`m`, `ready`, `rss`] strip_assume_tac) >>
  qexistsl_tac [`m`, `ready`, `rss`, `ra`, `rest`, `mem0`, `ret`, `srest`, `labs0`] >>
  simp[]
QED
