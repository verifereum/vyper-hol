(* Executable boundary for a selected call's emitted entry jump. *)
Theory functionInlinerSelectedEntry
Ancestors
  functionInlinerReachableCuts venomExecSemantics venomExecProofs
  dfAnalyzeProofs

Theorem inline_selected_jump_step:
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  ?tb dst entry_bb.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME tb /\
    get_instruction tb d.ic_index = SOME dst /\
    step_inst fuel ctx dst t =
      OK (jump_to (inline_cell_label_action frames eb.bb_label) t) /\
    lookup_block (inline_cell_label_action frames eb.bb_label)
      d.ic_function.fn_blocks = SOME entry_bb
Proof
  strip_tac >>
  drule_all inline_selected_jump_residual_entry_label >> strip_tac >>
  `?tb dst. lookup_block d.ic_block d.ic_function.fn_blocks = SOME tb /\
    get_instruction tb d.ic_index = SOME dst /\
    dst.inst_opcode = JMP /\
    dst.inst_operands = [Label (inline_cell_label_action frames eb.bb_label)] /\
    dst.inst_outputs = []` by
    (irule inline_selected_jump_residual_fetch >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`c`, `e`, `mid`] >> simp[]) >>
  `?entry_bb. lookup_block (inline_cell_label_action frames eb.bb_label)
      d.ic_function.fn_blocks = SOME entry_bb` by
    (gvs[venomInstTheory.fn_labels_def] >>
     drule dfAnalyzeProofsTheory.lookup_block_exists >> metis_tac[]) >>
  qexistsl_tac [`tb`, `dst`, `entry_bb`] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED
