Theory concretizeLayoutPhaseTerminal
Ancestors concretizeLayoutPhaseOrigin frameRankedTerminalCorridor

Theorem layout_terminal_phase_abort:
  layout_terminal_entry C g s t /\
  exec_block fuel C g.ltp_origin.lbo_source
    (layout_phase_normalize g.ltp_pending s) = Abort a post ==>
  ?post'. exec_block fuel C' g.ltp_origin.lbo_target
      (layout_phase_normalize g.ltp_pending t) = Abort a post' /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q (INR g) (INR g)
      (Abort a post) (Abort a post')
Proof
  simp[layout_terminal_entry_def, layout_phase_ok_abort_def] >>
  rpt strip_tac >> drule_all ranked_terminal_corridor_abort >> simp[]
QED

Theorem layout_terminal_phase_abort_ready:
  ~g.ltp_pending /\
  layout_phase_entry D lo vs0 C C' q0 es qs q (INR g) s t /\
  exec_block fuel C g.ltp_origin.lbo_source s = Abort a post ==>
  ?post'. exec_block fuel C' g.ltp_origin.lbo_target t = Abort a post' /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q (INR g) (INR g)
      (Abort a post) (Abort a post')
Proof
  simp[layout_phase_entry_def] >> strip_tac >>
  drule layout_terminal_phase_abort >> simp[] >> metis_tac[]
QED

val _ = export_theory();
