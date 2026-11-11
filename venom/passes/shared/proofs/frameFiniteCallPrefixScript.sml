Theory frameFiniteCallPrefix
Ancestors frameTerminalCallOrigins frameFiniteExecution venomExecSemantics
  venomInst

(* Finite completed calls extend the original block prefix without any
   hypothesis about the returned state's instruction cursor. *)
Theorem finite_step_terminal_call_edge:
  finite_step C i s (OK post) /\
  ~is_terminator i.inst_opcode /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  terminal_call_edge C bb s (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule (cj 1 finite_execution_realizable) >>
  strip_tac >> simp[terminal_call_edge_def] >>
  qexistsl [`post`, `n`] >> simp[]
QED

Theorem finite_step_terminal_call_prefix:
  finite_step C i s (OK post) /\
  ~is_terminator i.inst_opcode /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  terminal_call_prefix C bb s (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all finite_step_terminal_call_edge >>
  metis_tac[terminal_call_prefix_rules]
QED

Theorem finite_invoke_terminal_call_prefix_extend:
  terminal_call_prefix C bb start s /\
  finite_step C i s (OK post) /\ i.inst_opcode = INVOKE /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  terminal_call_prefix C bb start
    (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
  drule_all finite_step_terminal_call_prefix >>
  metis_tac[terminal_call_prefix_trans]
QED
