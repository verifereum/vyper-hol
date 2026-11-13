Theory concretizeLayoutExceptionalEntry
Ancestors frameTerminalCorridor contextCodegenRel frameRelocationValues
  venomExecSemantics venomState venomInst list arithmetic

Theorem layout_revert_forward_corridor:
  revert_forward_pair bb k j /\
  (!n i. get_instruction bb n = SOME i /\
    (i.inst_opcode = ASSIGN \/ i.inst_opcode = REVERT) ==>
    get_instruction bb' n = SOME i) ==>
  terminal_corridor bb bb' (SUC k) j
Proof
  simp[revert_forward_pair_def, terminal_corridor_def] >> rpt strip_tac
  >- metis_tac[] >>
  `n < LENGTH bb.bb_instructions` by
    (qpat_x_assum `get_instruction bb j = SOME _` mp_tac >>
     simp[get_instruction_def] >> rpt strip_tac >> decide_tac) >>
  `?i. get_instruction bb n = SOME i` by simp[get_instruction_def] >>
  `k < n` by decide_tac >>
  `i.inst_opcode = ASSIGN` by metis_tac[] >>
  metis_tac[]
QED

Theorem layout_returncopy_terminal_entry:
  terminal_corridor bb bb' (SUC s.vs_inst_idx) j /\
  s.vs_inst_idx = t.vs_inst_idx /\ variable_domains s t /\
  s.vs_labels = t.vs_labels /\ i.inst_opcode = RETURNDATACOPY /\
  step_inst_base i s = OK p /\ step_inst_base i t = OK q ==>
  terminal_entry bb bb' j (p with vs_inst_idx := SUC p.vs_inst_idx)
    (q with vs_inst_idx := SUC q.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base i s = OK p` mp_tac >>
  qpat_x_assum `step_inst_base i t = OK q` mp_tac >>
  simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[terminal_entry_def, variable_domains_def, write_memory_with_expansion_def,
    write_memory_def, lookup_var_def]
QED

Theorem layout_returncopy_terminal_abort:
  terminal_corridor bb bb' (SUC s.vs_inst_idx) j /\
  s.vs_inst_idx = t.vs_inst_idx /\ variable_domains s t /\
  s.vs_labels = t.vs_labels /\ i.inst_opcode = RETURNDATACOPY /\
  step_inst_base i s = OK p /\ step_inst_base i t = OK q /\
  exec_block fuel C bb (p with vs_inst_idx := SUC p.vs_inst_idx) = Abort a post ==>
  ?post'. exec_block fuel C' bb' (q with vs_inst_idx := SUC q.vs_inst_idx) =
      Abort a post' /\ dead_result_rel D (Abort a post) (Abort a post')
Proof
  strip_tac >> drule_all layout_returncopy_terminal_entry >>
  strip_tac >> drule_all terminal_entry_abort >> simp[]
QED

val _ = export_theory();
