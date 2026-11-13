Theory loadElimOccurrencePredecessor
Ancestors
  loadElimOccurrence loadElimOccurrenceInversion loadElimOccurrenceCoverage loadElimStaticGeneration
  loadElimPhiCapture venomExecSemantics venomExecProps venomExecProofs venomInst list

Theorem le_terminator_prev_bb:
  is_terminator j.inst_opcode /\ step_inst k C j t = OK u ==>
  u.vs_prev_bb = SOME t.vs_current_bb
Proof
  strip_tac >>
  `j.inst_opcode <> INVOKE` by
    (Cases_on `j.inst_opcode` >> gvs[is_terminator_def]) >>
  metis_tac[step_inst_non_invoke, step_inst_base_term_prev_bb]
QED

Theorem le_occ_prefix_phi_predecessor:
  wf_function fn /\ fn_inst_wf fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] ==>
  ?front prev j t k.
    pre = front ++ [StepOcc prev t.vs_inst_idx k t u] /\
    le_occ_prefix C fn s0 front j t /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME prev /\
    is_terminator j.inst_opcode /\ step_inst k C j t = OK u /\
    ~u.vs_halted /\ u.vs_prev_bb = SOME prev.bb_label /\
    MEM prev.bb_label (cfg_preds_of (cfg_analyze fn) bb.bb_label)
Proof
  strip_tac >>
  drule le_occ_prefix_phi_semantics >> strip_tac >>
  drule le_occ_prefix_phi_inversion >> strip_tac >> gvs[] >>
  rename1 `le_occ_prefix C fn s0 front j t` >>
  `active_inst fn j t` by metis_tac[le_occ_prefix_active] >>
  drule_all le_active_terminator_edge >> strip_tac >>
  `bb.bb_label = u.vs_current_bb /\ prev.bb_label = t.vs_current_bb` by
    metis_tac[lookup_block_label] >>
  drule_all le_static_edge_pred >> strip_tac >>
  drule_all le_terminator_prev_bb >> strip_tac >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected:
  wf_function fn /\ fn_inst_wf fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) result key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl ==>
  ?front prev j t k pairs v.
    pre = front ++ [StepOcc prev t.vs_inst_idx k t u] /\
    le_occ_prefix C fn s0 front j t /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME prev /\
    is_terminator j.inst_opcode /\ step_inst k C j t = OK u /\
    ~u.vs_halted /\ u.vs_prev_bb = SOME prev.bb_label /\
    MEM prev.bb_label (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
    pa.pa_phi_ops = mk_phi_ops_from_pairs pairs /\
    MAP FST pairs = cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl /\
    MEM (prev.bb_label,v) pairs /\
    FLOOKUP (unwrap_load_lattice (df_boundary NONE result prev.bb_label)) key =
      SOME [Var v]
Proof
  strip_tac >> drule_all le_occ_prefix_phi_predecessor >> strip_tac >>
  metis_tac[le_compute_phi_action_selected]
QED
