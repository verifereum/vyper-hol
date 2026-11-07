Theory concretizeLayoutCanonicalBlock
Ancestors concretizeLayoutCanonicalDeferred concretizeLayoutCanonicalBase
  concretizeLayoutCanonicalDriver
  concretizeLayoutPhaseCorridor concretizeLayoutPhaseOrigin frameRankedTerminalCorridor
  concretizeLayoutPairedEntry concretizeLayoutStagePairing concretizeStepStructure
  frameSelectedSimulation frameFiniteExecution venomExecSemantics venomInst
  fragExec concretizeMemLocDefs passSharedDefs list arithmetic

Theorem layout_canonical_corridor_instruction:
  ~g.ltp_pending /\ layout_corridor_entry C g s t /\
  get_instruction g.ltp_origin.lbo_source s.vs_inst_idx = SOME i ==>
  get_instruction g.ltp_origin.lbo_target t.vs_inst_idx = SOME i
Proof
  simp[layout_corridor_entry_def, layout_phase_normalize_def,
    ranked_terminal_entry_def, ranked_terminal_corridor_def] >> strip_tac >>
  Cases_on `g.ltp_remaining`
  >- gvs[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem layout_canonical_block_witness_step:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t a /\ get_instruction bb s.vs_inst_idx = SOME i ==>
  ?j. layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a /\
    (i.inst_opcode <> NOP ==> get_instruction bb' t.vs_inst_idx = SOME j)
Proof
  strip_tac >>
  Cases_on `a`
  >- (gvs[layout_canonical_block_witness_def] >>
      rename1 `layout_paired_ordinary _ _ _ _ _ _ _ _ _ positions _ _ _ _ _ _ g` >>
      `MEM i (fn_insts fn)` by
        (irule fragExecTheory.lookup_block_fn_insts >>
         goal_assum (drule_at Any) >>
         fs[get_instruction_def] >> metis_tac[EL_MEM]) >>
      `i.inst_opcode = NOP \/
       (concretize_inst_with_positions positions i).inst_opcode <> NOP` by
        (Cases_on `i.inst_opcode = ALLOCA`
         >- (fs[layout_driver_row_def] >>
             drule_all layout_stage_row_position >> strip_tac >>
             gvs[] >>
             simp[concretize_inst_with_positions_def, mk_assign_inst_def] >>
             Cases_on `i.inst_outputs` >> simp[] >>
             Cases_on `t'` >> simp[]) >>
         simp[concretize_positions_unchanged]) >>
      (qexists `concretize_inst_with_positions positions i` >>
      reverse conj_tac
      >- (strip_tac >> fs[layout_paired_ordinary_def] >>
          gvs[] >>
          drule_all concretizeLayoutBlockPairingTheory.layout_block_pair_lookup >> simp[]) >>
      simp[layout_canonical_step_witness_def] >>
      qexistsl [`bb`, `bb'`] >>
      simp[layout_canonical_block_witness_def] >>
      fs[layout_paired_ordinary_def] >> metis_tac[concretize_positions_nop])) >>
  gvs[layout_canonical_block_witness_def] >>
  drule_all layout_canonical_corridor_instruction >> strip_tac >>
  qexists `i` >>
  simp[layout_canonical_step_witness_def] >>
  qexistsl [`y.ltp_origin.lbo_source`, `y.ltp_origin.lbo_target`] >>
  simp[layout_canonical_block_witness_def]
QED

Theorem layout_canonical_block_step_choice:
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  layout_base_lookahead C q0 path q n i s ==>
  ?j. layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
    (i.inst_opcode <> NOP ==> get_instruction bb' t.vs_inst_idx = SOME j)
Proof
  simp[layout_canonical_EB_def] >> strip_tac >>
  drule_all layout_canonical_block_witness_step >>
  simp[layout_canonical_ES_def] >> metis_tac[]
QED

Theorem layout_canonical_block_witness_retained:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t a /\ get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> NOP /\ get_instruction bb' t.vs_inst_idx = SOME j ==>
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a
Proof
  strip_tac >> drule_all layout_canonical_block_witness_step >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem layout_canonical_step_lookup:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a /\ i.inst_opcode <> NOP ==>
  ?bb bb'. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t a /\ get_instruction bb s.vs_inst_idx = SOME i /\
    get_instruction bb' t.vs_inst_idx = SOME j
Proof
  simp[layout_canonical_step_witness_def] >> strip_tac >>
  Cases_on `a` >> gvs[]
  >- (drule_all concretizeLayoutBlockPairingTheory.layout_block_pair_lookup >>
      strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Theorem layout_canonical_block_exit_certificate:
  selected_block_exit_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
Proof
  rw[selected_block_exit_certificate_def] >>
  `layout_base_lookahead C q0 path q n i s` by
    (drule_all concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_exit >>
     simp[]) >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> simp[] >> rpt strip_tac >>
  `i.inst_opcode <> NOP` by
    (strip_tac >> qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frameFiniteJointDecorationTheory.decorated_step_cases,
       step_inst_base_def] >> metis_tac[]) >>
  `layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe
    (n + LENGTH w) r rs'` by
    (Cases_on `i.inst_opcode = INVOKE` >>
     Cases_on `r` >> Cases_on `rs'` >>
     gvs[layout_deferred_OS_def, layout_canonical_OS_def]) >>
  `!p. rs' <> OK p` by
    (Cases_on `r` >> Cases_on `rs'` >>
     gvs[layout_canonical_result_def]) >>

  simp[selected_block_match_def] >> qexists `rs'` >> conj_tac
  >- (irule finite_step_block_exit >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `r` >> Cases_on `rs'` >>
  gvs[layout_canonical_OB_def, layout_canonical_result_def]
QED

Theorem layout_canonical_term_certificate:
  selected_term_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
Proof
  rw[selected_term_certificate_def] >>
  `i.inst_opcode <> NOP /\ i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
  `layout_base_lookahead C q0 path q n i s` by
    simp[concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_term] >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> simp[] >> rpt strip_tac >>
  `w = [] /\ qe = q` by
    (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frameFiniteJointDecorationTheory.decorated_step_cases] >> metis_tac[]) >>
  gvs[layout_deferred_OS_def, layout_canonical_OS_def] >>
  Cases_on `rs'` >> gvs[layout_canonical_result_def] >>
  rename1 `finite_step C' j t (OK tp)` >>
  `?a. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t a` by (fs[layout_canonical_EB_def] >> metis_tac[]) >>
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a` by
    (irule layout_canonical_block_witness_retained >> simp[] >> metis_tac[]) >>
  first_assum (drule_then strip_assume_tac) >>
  `~post.vs_halted /\ ~tp.vs_halted /\ is_terminator j.inst_opcode` by
    fs[concretizeLayoutCompletedJumpTheory.layout_completed_jump_def] >>
  simp[selected_block_match_def] >> qexists `OK tp` >> conj_tac
  >- (drule_all finite_step_block_term >> simp[]) >>
  simp[layout_canonical_OB_def] >> rpt strip_tac >>
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a'` by
    (irule layout_canonical_block_witness_retained >> simp[] >> metis_tac[]) >>
  first_assum (drule_then strip_assume_tac) >>
  gvs[] >> qexistsl [`g'`, `i`, `j`, `s`, `t`] >>
  fs[layout_canonical_block_witness_def, layout_paired_ordinary_def]
QED

val _ = export_theory();
