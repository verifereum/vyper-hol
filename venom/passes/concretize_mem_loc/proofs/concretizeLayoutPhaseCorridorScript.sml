Theory concretizeLayoutPhaseCorridor
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutRankedCorridor frameRankedTerminalCorridor
  frameFiniteExecution frameTerminalCallOrigins venomExecSemantics venomState venomInst

Definition layout_corridor_entry_def:
  layout_corridor_entry C g s t <=>
    ranked_terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target g.ltp_remaining
      (layout_phase_normalize g.ltp_pending s)
      (layout_phase_normalize g.ltp_pending t) /\
    (!u. ~finite_block C g.ltp_origin.lbo_source g.ltp_origin.lbo_entry (OK u)) /\
    s.vs_halted = t.vs_halted
End

Theorem layout_corridor_origin_exclusion:
  layout_corridor_entry C g s t ==>
  ~finite_block C g.ltp_origin.lbo_source g.ltp_origin.lbo_entry (OK u)
Proof
  simp[layout_corridor_entry_def]
QED

Theorem layout_corridor_administrative:
  layout_corridor_entry C g s t ==>
  layout_corridor_entry C (g with ltp_pending := F)
    (layout_phase_normalize g.ltp_pending s)
    (layout_phase_normalize g.ltp_pending t)
Proof
  simp[layout_corridor_entry_def, layout_phase_normalize_def] >>
  Cases_on `g.ltp_pending` >> simp[]
QED

Theorem layout_corridor_assign:
  ~g.ltp_pending /\ layout_corridor_entry C g s t /\
  g.ltp_remaining = SUC n /\
  get_instruction g.ltp_origin.lbo_source s.vs_inst_idx = SOME i /\
  step_inst_base i s = OK p ==>
  ?q. get_instruction g.ltp_origin.lbo_target t.vs_inst_idx = SOME i /\
    step_inst_base i t = OK q /\
    layout_corridor_entry C (g with <|ltp_pending := T; ltp_remaining := n|>) p q
Proof
  rpt strip_tac >>
  `ranked_terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target
    (SUC n) s t` by
    gvs[layout_corridor_entry_def, layout_phase_normalize_def] >>
  drule_all ranked_terminal_entry_assign >> strip_tac >>
  `i.inst_opcode = ASSIGN` by
    (qpat_assum `ranked_terminal_entry _ _ _ s t` mp_tac >>
     pure_rewrite_tac[ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
     strip_tac >> qpat_x_assum `!d. _` (qspec_then `0` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `p.vs_halted = s.vs_halted /\ q.vs_halted = t.vs_halted` by
    (qpat_x_assum `step_inst_base i s = OK p` mp_tac >>
     qpat_x_assum `step_inst_base i t = OK q` mp_tac >>
     simp[Ntimes step_inst_base_def 2, AllCaseEqs()] >> rpt strip_tac >>
     gvs[update_var_def]) >>
  qexists_tac `q` >>
  gvs[layout_corridor_entry_def, layout_phase_normalize_def]
QED

Theorem layout_corridor_revert:
  ~g.ltp_pending /\ layout_corridor_entry C g s t /\
  g.ltp_remaining = 0 /\
  get_instruction g.ltp_origin.lbo_source s.vs_inst_idx = SOME i /\
  step_inst_base i s = Abort a post ==>
  ?post'. get_instruction g.ltp_origin.lbo_target t.vs_inst_idx = SOME i /\
    step_inst_base i t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  rpt strip_tac >> irule ranked_terminal_entry_revert >>
  goal_assum (drule_at Any) >>
  gvs[layout_corridor_entry_def, layout_phase_normalize_def] >>
  qexists_tac `g.ltp_origin.lbo_source` >> simp[]
QED

Theorem layout_corridor_copy_entry:
  terminal_call_prefix C origin.lbo_source origin.lbo_entry s /\
  revert_forward_at origin.lbo_source s.vs_inst_idx /\
  ranked_terminal_corridor origin.lbo_source origin.lbo_target
    (SUC s.vs_inst_idx) (SUC t.vs_inst_idx) n /\
  variable_domains s t /\
  s.vs_labels = t.vs_labels /\ s.vs_halted = t.vs_halted /\
  i.inst_opcode = RETURNDATACOPY /\
  step_inst_base i s = OK p /\ step_inst_base i t = OK q ==>
  layout_corridor_entry C
    <|ltp_origin := origin; ltp_pending := T; ltp_remaining := n|> p q
Proof
  rpt strip_tac >>
  `ranked_terminal_entry origin.lbo_source origin.lbo_target n
    (p with vs_inst_idx := SUC p.vs_inst_idx)
    (q with vs_inst_idx := SUC q.vs_inst_idx)` by
    (drule_all layout_returncopy_ranked_entry >> simp[]) >>
  `!u. ~finite_block C origin.lbo_source origin.lbo_entry (OK u)` by
    (gen_tac >> irule terminal_call_revert_no_finite_ok >>
     goal_assum (drule_at Any) >> simp[]) >>
  `p.vs_halted = q.vs_halted` by
    (qpat_x_assum `step_inst_base i s = OK p` mp_tac >>
     qpat_x_assum `step_inst_base i t = OK q` mp_tac >>
     simp[Ntimes step_inst_base_def 2, AllCaseEqs()] >> rpt strip_tac >>
     gvs[write_memory_with_expansion_def, write_memory_def]) >>
  simp[layout_corridor_entry_def, layout_phase_normalize_def]
QED

val _ = export_theory();
