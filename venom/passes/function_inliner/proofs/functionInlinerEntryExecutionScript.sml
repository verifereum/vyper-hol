(* Execute the emitted selected-call jump at the actual incoming control cell.
   Entry PHIs and parameter assignments are deliberately left to consumers. *)
Theory functionInlinerEntryExecution
Ancestors
  functionInlinerSelectedEntry functionInlinerSimulation
  functionInlinerReachableCuts functionInlinerFrame
  venomExecSemantics venomExecProofs venomState venomInst stateFrame

Theorem inline_selected_entry_exec_block:
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  t.vs_current_bb = d.ic_block /\ t.vs_inst_idx = d.ic_index /\
  ~t.vs_halted ==>
  ?tb dst entry_bb u.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME tb /\
    get_instruction tb d.ic_index = SOME dst /\
    step_inst fuel ctx dst t = OK u /\
    exec_block fuel ctx tb t = OK u /\
    u = jump_to (inline_cell_label_action frames eb.bb_label) t /\
    lookup_block (inline_cell_label_action frames eb.bb_label)
      d.ic_function.fn_blocks = SOME entry_bb /\
    u.vs_current_bb = inline_cell_label_action frames eb.bb_label /\
    u.vs_prev_bb = SOME t.vs_current_bb /\
    u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    inline_shared_frame u = inline_shared_frame t /\
    inline_caller_residual u = inline_caller_residual t
Proof
  strip_tac >>
  drule_all inline_selected_jump_step >>
  disch_then (qspecl_then [`t`, `fuel`, `ctx`] strip_assume_tac) >>
  `?jb ji. lookup_block d.ic_block d.ic_function.fn_blocks = SOME jb /\
    get_instruction jb d.ic_index = SOME ji /\
    ji.inst_opcode = JMP /\
    ji.inst_operands = [Label (inline_cell_label_action frames eb.bb_label)] /\
    ji.inst_outputs = []` by
    (irule inline_selected_jump_residual_fetch >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`c`, `e`, `mid`] >> simp[]) >>
  gvs[] >>
  simp[Once exec_block_def, is_terminator_def, jump_to_def,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def]
QED
