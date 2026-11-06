Theory concretizeLayoutRunEntry
Ancestors concretizeLayoutRunState concretizeLayoutScopedEntry
  concretizeLayoutPhaseOrigin concretizeLayoutScopedPhase
  venomExecSemantics venomState contextCodegenRel

Theorem layout_scoped_enters_entry:
  enters_block fn s p /\ enters_block fn' t p' /\ ~a.lop_pending /\
  layout_ordinary_trace vs0 C q0 es qs q a p /\
  layout_ordinary_state D lo C' q0 es qs a p p' ==>
  ?bb bb' phi phi' b.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis s bb.bb_instructions = OK phi /\
    eval_phis t bb'.bb_instructions = OK phi' /\
    p = (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    p' = (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    b = (a with lop_origin :=
      <|lbo_source := bb; lbo_target := bb'; lbo_entry := p|>) /\
    layout_ordinary_entry D lo vs0 C C' q0 es qs q b p p' /\
    layout_scoped_phi_link g (INL b) fn fn' s t bb bb' phi phi'
Proof
  simp[enters_block_def] >> strip_tac >>
  drule_all layout_scoped_install_origin >> strip_tac >>
  metis_tac[]
QED

val _ = export_theory();
