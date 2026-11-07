Theory concretizeLayoutCanonicalBlock
Ancestors concretizeLayoutCanonicalDeferred concretizeLayoutCanonicalBase
  concretizeLayoutCanonicalDriver concretizeLayoutAlignedControl concretizeLayoutPhaseCompose
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

Theorem layout_canonical_success_ready:
  layout_canonical_success D lo vs0 C C' q0 es qs ass qend m invoke a p tp /\
  qn = EL (SUC m) (q0::qs) ==>
  ?b. layout_phase_origin b = layout_phase_origin a /\
    layout_canonical_entry D lo vs0 C C' q0 es qs ass qend
      qn (SUC m) b
      (p with vs_inst_idx := SUC p.vs_inst_idx)
      (tp with vs_inst_idx := SUC tp.vs_inst_idx)
Proof
  simp[layout_canonical_success_def] >> strip_tac >>
  Cases_on `b`
  >- (gvs[] >>
      rename1 `layout_driver_indexed es ass k` >>
      qexists `INL (k with lop_pending := F)` >>
      simp[layout_phase_origin_def, layout_canonical_entry_def] >>
      fs[layout_aligned_entry_def] >>
      drule layout_ordinary_administrative >> strip_tac >>
      Cases_on `invoke` >>
      gvs[layout_canonical_ready_def, layout_aligned_entry_def,
         layout_ordinary_entry_def, layout_ordinary_trace_def,
         layout_phase_normalize_def, layout_phase_origin_def, layout_driver_indexed_def,
         concretizeLayoutCanonicalIndexTheory.layout_phase_canonical_def]) >>
  gvs[] >> qexists `INR (y with ltp_pending := F)` >>
  simp[layout_phase_origin_def, layout_canonical_entry_def] >>
  drule layout_corridor_administrative >> gvs[layout_phase_origin_def]
QED

Theorem layout_canonical_corridor_next:
  ~g.ltp_pending /\ layout_corridor_entry C g s t /\
  get_instruction g.ltp_origin.lbo_source s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ finite_step C i s (OK p) ==>
  ?k tp. k.ltp_origin = g.ltp_origin /\ ~k.ltp_pending /\
    get_instruction g.ltp_origin.lbo_target t.vs_inst_idx = SOME i /\
    finite_step C' i t (OK tp) /\
    p.vs_inst_idx = s.vs_inst_idx /\ tp.vs_inst_idx = t.vs_inst_idx /\
    layout_corridor_entry C k
      (p with vs_inst_idx := SUC s.vs_inst_idx)
      (tp with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `ranked_terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target
     g.ltp_remaining s t` by
    gvs[layout_corridor_entry_def, layout_phase_normalize_def] >>
  Cases_on `g.ltp_remaining`
  >- (fs[ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
      gvs[] >> fs[is_terminator_def]) >>
  `i.inst_opcode = ASSIGN` by
    (fs[ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  `step_inst_base i s = OK p` by
    (qpat_x_assum `finite_step C i s (OK p)` mp_tac >>
     simp[Once finite_step_cases] >> metis_tac[]) >>
  drule_all layout_corridor_assign >> strip_tac >>
  `p.vs_inst_idx = s.vs_inst_idx /\ q.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[step_inst_base_preserves_inst_idx, is_terminator_def] >>
  drule layout_corridor_administrative >> simp[] >> strip_tac >>
  qexistsl [`g with <|ltp_pending := F; ltp_remaining := n|>`, `q`] >>
  simp[] >> irule finite_step_base >> simp[]
QED

Theorem layout_canonical_retained_reenter:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t (INL a) /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL a) /\
  i.inst_opcode <> NOP /\ get_instruction bb s.vs_inst_idx = SOME i /\
  decoration_at fn i s q /\ decoration_entry fn sn qn /\
  sn.vs_current_bb = s.vs_current_bb /\
  sn.vs_inst_idx = SUC s.vs_inst_idx /\ tn.vs_inst_idx = SUC t.vs_inst_idx /\
  layout_phase_origin b = a.lop_origin /\
  layout_canonical_entry D lo vs0 C C' q0 es qs ass qend qn m b sn tn ==>
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    qn m bb sn bb' tn b
Proof
  Cases_on `b`
  >- (simp[layout_canonical_block_witness_def,
        layout_canonical_step_witness_def, layout_canonical_entry_def,
        layout_canonical_ready_def, layout_phase_origin_def,
        layout_paired_ordinary_def] >> strip_tac >>
      Cases_on `q` >>
      gvs[frameFiniteJointDecorationTheory.decoration_entry_def,
          frameFiniteJointDecorationTheory.decoration_at_def] >>
      rename1 `(concretize_inst_with_positions pp i).inst_opcode <> NOP` >>
      qmatch_asmsub_rename_tac `layout_driver_row C' fn ft pp` >>
      qexistsl [`fn`, `ft`, `pp`] >> simp[] >>
      qpat_x_assum `layout_block_pair pp _ _ _ _` mp_tac >>
      disch_then (mp_then Any mp_tac
        concretizeLayoutBlockPairingTheory.layout_block_pair_advance) >>
      simp[ADD1] >> metis_tac[]) >>
  simp[layout_canonical_block_witness_def, layout_paired_ordinary_def,
       layout_canonical_entry_def, layout_phase_origin_def] >> metis_tac[]
QED

Theorem layout_canonical_retained_successor:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t a /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> NOP /\
  ~is_terminator i.inst_opcode /\ decoration_at fn i s q /\
  decoration_entry fn (p with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  finite_step C i s (OK p) /\ finite_step C' j t (OK tp) /\
  get_instruction bb' t.vs_inst_idx = SOME j /\
  layout_canonical_success D lo vs0 C C' q0 es qs ass qend m
    (i.inst_opcode = INVOKE) a p tp /\
  qn = EL (SUC m) (q0::qs) ==>
  ?b. layout_phase_origin b = layout_phase_origin a /\ (ISL b ==> ISL a) /\
    layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      qn (SUC m) bb (p with vs_inst_idx := SUC s.vs_inst_idx) bb'
      (tp with vs_inst_idx := SUC t.vs_inst_idx) b
Proof
  strip_tac >>
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a` by
    (irule layout_canonical_block_witness_retained >> metis_tac[]) >>
  Cases_on `a`
  >- (`~is_terminator j.inst_opcode` by
        (fs[layout_canonical_step_witness_def] >>
         gvs[] >> metis_tac[concretize_positions_nonterminator]) >>
      `p.vs_current_bb = s.vs_current_bb /\ p.vs_inst_idx = s.vs_inst_idx /\
       tp.vs_inst_idx = t.vs_inst_idx` by
        metis_tac[frameFiniteControlTheory.finite_step_nonterminator_control] >>
      drule_all layout_canonical_success_ready >> strip_tac >>
      gvs[layout_phase_origin_def] >> qexists `b` >> simp[] >>
      irule layout_canonical_retained_reenter >> simp[] >>
      qexistsl [`x`, `fn`, `i`, `j`, `n`, `q`, `s`, `t`] >> simp[]) >>
  `~y.ltp_pending /\ layout_corridor_entry C y s t /\
   y.ltp_origin.lbo_source = bb /\ y.ltp_origin.lbo_target = bb'` by
    fs[layout_canonical_block_witness_def] >>
  gvs[] >> drule_all layout_canonical_corridor_next >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  `i = j` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `i.inst_opcode <> INVOKE` by
    (fs[layout_corridor_entry_def, layout_phase_normalize_def,
        ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
     Cases_on `y.ltp_remaining` >> gvs[] >>
     qpat_x_assum `!d. d < SUC _ ==> _` (qspec_then `0` mp_tac) >>
     simp[] >> metis_tac[]) >>
  gvs[finite_step_iff, step_inst_def] >>
  qexists `INR k` >> simp[layout_phase_origin_def,
    layout_canonical_block_witness_def]
QED

Theorem layout_canonical_block_outcome_transport:
  (!a. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      q n bb s bb' t a ==>
    ?b. layout_phase_origin b = layout_phase_origin a /\ (ISL b ==> ISL a) /\
      layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
        qn nn bb sn bb' tn b) /\
  layout_canonical_OB D lo vs0 C C' q0 es qs ass qend
    qn nn qe m bb sn bb' tn r r' ==>
  layout_canonical_OB D lo vs0 C C' q0 es qs ass qend
    q n qe m bb s bb' t r r'
Proof
  strip_tac >> Cases_on `r` >> Cases_on `r'` >>
  gvs[layout_canonical_OB_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `a` >> gvs[layout_phase_origin_def] >> metis_tac[]
QED

Theorem layout_canonical_retained_next:
  qs = MAP SND path /\ i.inst_opcode <> NOP /\
  decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  decorated_step C i s (OK post) q n ws qm ds /\
  ~is_terminator i.inst_opcode /\ decoration_consumes C i q post qm ev qn /\
  decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
    r qn (n+LENGTH ws+1) wb qe db /\
  selected_segment C q0 path n q (ws++[(ev,qn)]++wb) qe /\
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t ==>
  ?j. layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
    (!rs'. finite_step C' j t rs' /\
      layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend
        q n qm (n+LENGTH ws) i s j t (OK post) rs' ==>
      ?tb. layout_canonical_EB D lo vs0 C C' q0 es qs ass qend qn
          (n+LENGTH ws+1) bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
        (!rb'. finite_block C' bb' tb rb' /\
          layout_canonical_OB D lo vs0 C C' q0 es qs ass qend qn
            (n+LENGTH ws+1) qe (n+LENGTH ws+1+LENGTH wb) bb
            (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb r rb' ==>
          selected_block_match C'
            (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
            q n (ws++[(ev,qn)]++wb) qe bb s bb' t r))
Proof
  strip_tac >>
  `layout_base_lookahead C q0 path q n i s` by
    (irule concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_next >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> simp[] >> rpt strip_tac >>
  Cases_on `rs'` >>
  gvs[layout_deferred_OS_def, layout_canonical_OS_def, layout_canonical_result_def] >>
  `joint_segment C q ws qm /\ joint_segment C qn wb qe /\
   joint_transition C qm ev qn` by
    metis_tac[frameFiniteJointDecorationTheory.decorated_execution_segment,
      frameFiniteJointDecorationTheory.decoration_consumes_def] >>
  `qn = EL (SUC (n + LENGTH ws)) (q0::MAP SND path)` by
    (fs[APPEND_ASSOC] >>
     drule_all (SRULE[APPEND_ASSOC] frameSelectedDecorationTheory.selected_segment_edge) >>
     strip_tac >> gvs[GSYM ADD_ASSOC, GSYM ADD1, ADD_CLAUSES]) >>
  `selected_segment C q0 path (n+LENGTH ws) qm [(ev,qn)] qn` by
    (irule (cj 1 frameSelectedDecorationTheory.selected_segment_parts) >>
     simp[frameFiniteJointDecorationTheory.joint_segment_def] >>
     qexistsl [`qe`, `wb`] >> conj_tac >- fs[] >>
     irule (cj 2 frameSelectedDecorationTheory.selected_segment_parts) >>
     fs[frameFiniteJointDecorationTheory.joint_segment_def] >>
     qexists `q` >> simp[] >>
     qpat_x_assum `selected_segment _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  `!a. layout_canonical_step_witness D lo vs0 C C' q0 es (MAP SND path) ass qend
      q n i s j t a ==>
    layout_canonical_success D lo vs0 C C' q0 es (MAP SND path) ass qend
      (n+LENGTH ws) (i.inst_opcode = INVOKE) a post v` by
    (Cases_on `i.inst_opcode = INVOKE` >> gvs[] >> metis_tac[]) >>
  `finite_step C i s (OK post)` by
    metis_tac[frameFiniteJointDecorationTheory.decorated_execution_erases] >>
  `~is_terminator j.inst_opcode` by
    (qhdtm_x_assum `layout_canonical_ES` mp_tac >>
     simp[layout_canonical_ES_def] >> strip_tac >>
     qhdtm_x_assum `layout_canonical_step_witness` mp_tac >>
     simp[layout_canonical_step_witness_def] >> strip_tac >>
     Cases_on `a` >> gvs[]
     >- simp[concretize_positions_nonterminator] >>
     fs[layout_canonical_block_witness_def] >> gvs[] >>
     drule_all layout_canonical_corridor_instruction >> strip_tac >> gvs[]) >>
  `!a. layout_canonical_block_witness D lo vs0 C C' q0 es (MAP SND path) ass qend
      q n bb s bb' t a ==>
    ?b. layout_phase_origin b = layout_phase_origin a /\ (ISL b ==> ISL a) /\
      layout_canonical_block_witness D lo vs0 C C' q0 es (MAP SND path) ass qend
        qn (SUC (n+LENGTH ws)) bb (post with vs_inst_idx := SUC s.vs_inst_idx)
        bb' (v with vs_inst_idx := SUC t.vs_inst_idx) b` by
    (rpt strip_tac >> irule layout_canonical_retained_successor >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     fs[] >> metis_tac[layout_canonical_block_witness_retained]) >>
  qexists `v with vs_inst_idx := SUC t.vs_inst_idx` >> conj_tac
  >- (simp[layout_canonical_EB_def, ADD1] >>
      fs[layout_canonical_EB_def, ADD1] >> metis_tac[]) >>
  rpt strip_tac >> simp[selected_block_match_def] >> qexists `rb'` >> conj_tac
  >- (irule finite_step_block_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule layout_canonical_block_outcome_transport >>
  goal_assum (drule_at Any) >> fs[ADD1] >> metis_tac[]
QED

val _ = export_theory();
