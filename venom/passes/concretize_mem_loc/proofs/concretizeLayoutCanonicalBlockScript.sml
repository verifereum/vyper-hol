Theory concretizeLayoutCanonicalBlock
Ancestors concretizeLayoutCutSafe concretizeLayoutCanonicalDeferred concretizeLayoutCanonicalBase
  concretizeLayoutCanonicalDriver concretizeLayoutAlignedControl concretizeLayoutPhaseCompose
  concretizeLayoutPhaseCorridor concretizeLayoutPhaseOrigin frameRankedTerminalCorridor
  concretizeLayoutPairedEntry concretizeLayoutStagePairing concretizeStepStructure
  frameSelectedPrefix frameSelectedSimulation frameSelectedDecoration frameFiniteJointDecoration
  frameGasEvents fmpAnalysisProps frameFiniteExecution venomExecSemantics venomInst
  fragExec concretizeMemLocDefs passSharedDefs list arithmetic
  mem2varRevertForward makeSsaRfShape analysisSimProofsBase
  concretizeLayoutCanonicalBaseMemory concretizeLayoutCanonicalBaseCertificate

Theorem layout_prefix_alias_success:
  (!p q. same_after_assigns xs p q ==> eval_operand p s = eval_operand q s) /\
  step_inst fuel C i s = OK post /\ ~is_terminator i.inst_opcode ==>
  (!p q. same_after_assigns (i::xs) p q ==>
    eval_operand p post = eval_operand q post)
Proof
  rpt strip_tac >>
  Cases_on `p = q` >- gvs[] >>
  Cases_on `step_back_assign i p` >>
  Cases_on `step_back_assign i q` >>
  gvs[contextCodegenRelTheory.same_after_assigns_def] >>
  imp_res_tac m2v_step_back_assign_eval >>
  metis_tac[]
QED

Theorem layout_prefix_alias_index:
  (!p q. same_after_assigns xs p q ==> eval_operand p s = eval_operand q s) ==>
  (!p q. same_after_assigns xs p q ==>
    eval_operand p (s with vs_inst_idx := k) =
    eval_operand q (s with vs_inst_idx := k))
Proof
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem layout_prefix_alias_initialize:
  !is s p q.
    same_after_assigns (REVERSE (TAKE (phi_prefix_length is) is)) p q ==>
    eval_operand p s = eval_operand q s
Proof
  rpt gen_tac >>
  `EVERY (\i. i.inst_opcode <> ASSIGN)
     (REVERSE (TAKE (phi_prefix_length is) is))` by
    (simp[rich_listTheory.EVERY_REVERSE, EVERY_MEM] >>
     mp_tac (Q.SPEC `is` phi_prefix_all_phi) >>
     simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  simp[simplifyCfgFrameRfTheory.scfg_same_after_nonassigns]
QED

Theorem layout_prefix_alias_phi_reset:
  !is k p q.
    phi_prefix_length is <= k /\ k <= LENGTH is /\
    same_after_assigns (REVERSE (TAKE k is)) p q ==>
    same_after_assigns
      (REVERSE (TAKE (k - phi_prefix_length is)
        (DROP (phi_prefix_length is) is))) p q
Proof
  rpt strip_tac >>
  `TAKE k is = TAKE (phi_prefix_length is) is ++
     TAKE (k - phi_prefix_length is) (DROP (phi_prefix_length is) is)` by
    (qspecl_then [`phi_prefix_length is`, `k - phi_prefix_length is`, `is`]
       mp_tac TAKE_SUM >> simp[]) >>
  qpat_x_assum `same_after_assigns _ _ _` mp_tac >>
  asm_rewrite_tac[REVERSE_APPEND] >>
  strip_tac >>
  irule rf_same_after_drop_phi_suffix >>
  goal_assum (drule_at Any) >>
  simp[rich_listTheory.EVERY_REVERSE, phi_prefix_all_phi]
QED

Theorem layout_prefix_alias_concretize:
  !xs positions p q.
    same_after_assigns xs p q ==>
    same_after_assigns
      (FILTER (\i. i.inst_opcode <> NOP)
        (MAP (concretize_inst_with_positions positions) xs)) p q
Proof
  Induct_on `xs`
  >- simp[contextCodegenRelTheory.same_after_assigns_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `p = q`
  >- simp[makeSsaRfWitnessTheory.rf_same_after_assigns_refl] >>
  Cases_on `h.inst_opcode = ALLOCA`
  >- (Cases_on `p` >> Cases_on `q` >>
      gvs[contextCodegenRelTheory.same_after_assigns_def,
        contextCodegenRelTheory.step_back_assign_def,
        SF boolSimps.COND_elim_ss] >>
      Cases_on `h.inst_outputs` >>
      simp[concretize_inst_with_positions_def] >>
      Cases_on `t` >>
      Cases_on `FLOOKUP positions (Allocation h.inst_id)` >>
      gvs[mk_assign_inst_def, mk_nop_inst_def] >> metis_tac[]) >>
  gvs[concretize_inst_with_positions_def] >>
  Cases_on `h.inst_opcode = NOP`
  >- (Cases_on `p` >> Cases_on `q` >>
      gvs[contextCodegenRelTheory.same_after_assigns_def,
        contextCodegenRelTheory.step_back_assign_def,
        SF boolSimps.COND_elim_ss] >> metis_tac[]) >>
  Cases_on `step_back_assign h p` >>
  Cases_on `step_back_assign h q` >>
  gvs[contextCodegenRelTheory.same_after_assigns_def]
QED

Definition layout_paired_prefix_alias_def:
  layout_paired_prefix_alias bb s bb' t <=>
    (!p q. same_after_assigns
      (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) p q ==>
      eval_operand p s = eval_operand q s) /\
    (!p q. same_after_assigns
      (REVERSE (TAKE t.vs_inst_idx bb'.bb_instructions)) p q ==>
      eval_operand p t = eval_operand q t)
End

Theorem layout_paired_prefix_alias_initialize:
  s.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
  t.vs_inst_idx = phi_prefix_length bb'.bb_instructions ==>
  layout_paired_prefix_alias bb s bb' t
Proof
  simp[layout_paired_prefix_alias_def] >>
  metis_tac[layout_prefix_alias_initialize]
QED

Theorem layout_prefix_alias_advance[local]:
  (!a b. same_after_assigns
    (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) a b ==>
    eval_operand a s = eval_operand b s) /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  finite_step C i s (OK p) /\ ~is_terminator i.inst_opcode ==>
  (!a b. same_after_assigns
    (REVERSE (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) a b ==>
    eval_operand a (p with vs_inst_idx := SUC s.vs_inst_idx) =
    eval_operand b (p with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  simp[get_instruction_def, finite_step_iff] >> rpt strip_tac >>
  gvs[rich_listTheory.TAKE_SUC_BY_TAKE, REVERSE_SNOC] >>
  metis_tac[layout_prefix_alias_success, layout_prefix_alias_index]
QED

Theorem layout_paired_prefix_alias_retained:
  layout_paired_prefix_alias bb s bb' t /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  get_instruction bb' t.vs_inst_idx = SOME j /\
  finite_step C i s (OK p) /\ finite_step C' j t (OK tp) /\
  ~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode ==>
  layout_paired_prefix_alias bb (p with vs_inst_idx := SUC s.vs_inst_idx)
    bb' (tp with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[layout_paired_prefix_alias_def] >> rpt strip_tac >>
  irule layout_prefix_alias_advance >> metis_tac[]
QED

Theorem layout_paired_prefix_alias_nop:
  layout_paired_prefix_alias bb s bb' t /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode = NOP ==>
  layout_paired_prefix_alias bb (s with vs_inst_idx := SUC s.vs_inst_idx) bb' t
Proof
  simp[layout_paired_prefix_alias_def, get_instruction_def] >>
  rpt strip_tac >>
  gvs[rich_listTheory.TAKE_SUC_BY_TAKE, REVERSE_SNOC,
    instIdxIndepTheory.eval_op_inst_idx,
    contextCodegenRelTheory.same_after_assigns_def,
    contextCodegenRelTheory.step_back_assign_def] >>
  Cases_on `p` >> Cases_on `q` >>
  gvs[AllCaseEqs(), SF boolSimps.COND_elim_ss] >> metis_tac[]
QED

Theorem layout_filter_rank_take[local]:
  !R P xs k.
  TAKE (LENGTH (FILTER P (MAP R (TAKE k xs))))
    (FILTER P (MAP R xs)) = FILTER P (MAP R (TAKE k xs))
Proof
  rpt gen_tac >> qid_spec_tac `k` >> Induct_on `xs` >> simp[] >>
  Cases_on `k` >> simp[] >> Cases_on `P (R h)` >> simp[]
QED

Theorem layout_paired_prefix_alias_source_demand:
  layout_block_pair positions bb bb' s.vs_inst_idx t.vs_inst_idx /\
  layout_paired_prefix_alias bb s bb' t /\
  same_after_assigns (REVERSE (TAKE s.vs_inst_idx bb.bb_instructions)) p q ==>
  eval_operand p s = eval_operand q s /\
  eval_operand p t = eval_operand q t
Proof
  simp[layout_paired_prefix_alias_def,
    concretizeLayoutBlockPairingTheory.layout_block_pair_def] >>
  rpt strip_tac >>
  drule layout_prefix_alias_concretize >>
  disch_then (qspec_then `positions` mp_tac) >>
  gvs[clear_nops_block_def, passTransformTheory.block_map_transform_def,
    concretizeLayoutBlockPairingTheory.layout_filter_rank_def,
    layout_filter_rank_take, GSYM MAP_REVERSE, GSYM FILTER_REVERSE] >>
  metis_tac[]
QED

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

Theorem layout_canonical_run_fn_name:
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t ==>
  fn'.fn_name = fn.fn_name
Proof
  simp[layout_canonical_run_def, layout_driver_row_def] >>
  metis_tac[fmpAnalysisPropsTheory.lookup_function_name]
QED

Theorem layout_canonical_block_exit_execution:
  decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  decorated_step C i s r q n w qe ds /\ (!post. r <> OK post) /\
  selected_segment C q0 path n q w qe /\
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t ==>
  ?j. layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
    (!rs'. finite_step C' j t rs' /\
      layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend
        q n qe (n+LENGTH w) i s j t r rs' ==>
      selected_block_match C'
        (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
        q n w qe bb s bb' t r /\
      (!k. step_inst k C' j t = rs' ==> exec_block k C' bb' t = rs'))
Proof
  strip_tac >>
  `layout_base_lookahead C q0 path q n i s` by
    (drule_all concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_exit >>
     simp[]) >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> simp[] >> gen_tac >> strip_tac >>
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

  conj_tac
  >- (simp[selected_block_match_def] >> qexists `rs'` >> conj_tac
      >- (irule finite_step_block_exit >> goal_assum (drule_at Any) >> simp[]) >>
      Cases_on `r` >> Cases_on `rs'` >>
      gvs[layout_canonical_OB_def, layout_canonical_result_def]) >>
  rpt strip_tac >> simp[Once exec_block_def] >> Cases_on `rs'` >> gvs[]
QED

Theorem layout_canonical_term_execution:
  decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  decorated_step C i s (OK post) q n w qe ds /\ is_terminator i.inst_opcode /\
  selected_segment C q0 path n q w qe /\
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t ==>
  ?j. layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
    (!rs'. finite_step C' j t rs' /\
      layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend
        q n qe (n+LENGTH w) i s j t (OK post) rs' ==>
      selected_block_match C'
        (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
        q n w qe bb s bb' t (if post.vs_halted then Halt post else OK post) /\
      (!k. step_inst k C' j t = rs' ==> exec_block k C' bb' t = rs'))
Proof
  strip_tac >>
  `i.inst_opcode <> NOP /\ i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
  `layout_base_lookahead C q0 path q n i s` by
    simp[concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_term] >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> simp[] >> gen_tac >> strip_tac >>
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
  conj_tac
  >- (simp[selected_block_match_def] >> qexists `OK tp` >> conj_tac
      >- (drule_all finite_step_block_term >> simp[]) >>
      simp[layout_canonical_OB_def] >> rpt strip_tac >>
      `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
        q n i s j t a'` by
        (irule layout_canonical_block_witness_retained >> simp[] >> metis_tac[]) >>
      first_assum (drule_then strip_assume_tac) >>
      gvs[] >> qexistsl [`g'`, `i`, `j`, `s`, `t`] >>
      fs[layout_canonical_block_witness_def, layout_paired_ordinary_def]) >>
  rpt strip_tac >> simp[Once exec_block_def]
QED





Theorem layout_canonical_block_exit_certificate_fuel:
  selected_block_exit_certificate_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
    (events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend))
Proof
  pure_rewrite_tac[selected_block_exit_certificate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  `layout_base_lookahead C q0 path q n i s` by
    (drule_all concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_exit >>
     simp[]) >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  `i.inst_opcode <> NOP` by
    (strip_tac >> qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frameFiniteJointDecorationTheory.decorated_step_cases,
       step_inst_base_def] >> metis_tac[]) >>
  qpat_x_assum `events_OS _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [events_OS_def]) >>
  `layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe
    (n + LENGTH w) r rs'` by
    (Cases_on `i.inst_opcode = INVOKE` >>
     Cases_on `r` >> Cases_on `rs'` >>
     gvs[layout_deferred_OS_def, layout_canonical_OS_def]) >>
  `!p. rs' <> OK p` by
    (Cases_on `r` >> Cases_on `rs'` >>
     gvs[layout_canonical_result_def]) >>
  `block_events_agree C C' bb s bb' t r rs'` by
    (irule block_events_agree_exit >>
     `finite_step C i s r` by
       metis_tac[frameFiniteJointDecorationTheory.decorated_execution_erases] >>
     metis_tac[]) >>
  pure_rewrite_tac[selected_block_match_fuel_def, events_OB_def] >> qexists `rs'` >> conj_tac
  >- (simp[Once exec_block_def] >> Cases_on `rs'` >> gvs[]) >>
  conj_tac
  >- (irule finite_step_block_exit >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `r` >> Cases_on `rs'` >>
  gvs[layout_canonical_OB_def, layout_canonical_result_def]
QED

Theorem layout_canonical_term_certificate_fuel:
  selected_term_certificate_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
    (events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend))
Proof
  pure_rewrite_tac[selected_term_certificate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  `i.inst_opcode <> NOP /\ i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
  `layout_base_lookahead C q0 path q n i s` by
    simp[concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_term] >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  `w = [] /\ qe = q` by
    (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frameFiniteJointDecorationTheory.decorated_step_cases] >> metis_tac[]) >>
  qpat_x_assum `events_OS _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [events_OS_def]) >>
  gvs[layout_deferred_OS_def, layout_canonical_OS_def] >>
  Cases_on `step_inst k C' j t` >> gvs[layout_canonical_result_def] >>
  rename1 `finite_step C' j t (OK tp)` >>
  `?a. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t a` by (fs[layout_canonical_EB_def] >> metis_tac[]) >>
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a` by
    (irule layout_canonical_block_witness_retained >> simp[] >> metis_tac[]) >>
  first_assum (drule_then strip_assume_tac) >>
  `~post.vs_halted /\ ~tp.vs_halted /\ is_terminator j.inst_opcode` by
    fs[concretizeLayoutCompletedJumpTheory.layout_completed_jump_def] >>
  `!r r'. block_events_agree C C' bb s bb' t r r'` by
    (rpt gen_tac >> irule block_events_agree_term >>
     `finite_step C i s (OK post)` by
       metis_tac[frameFiniteJointDecorationTheory.decorated_execution_erases] >>
     metis_tac[]) >>
  pure_rewrite_tac[selected_block_match_fuel_def, events_OB_def] >> qexists `OK tp` >> conj_tac
  >- simp[Once exec_block_def] >>
  conj_tac
  >- (drule_all finite_step_block_term >> simp[]) >>
  simp[layout_canonical_OB_def] >> rpt strip_tac >>
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a'` by
    (irule layout_canonical_block_witness_retained >> simp[] >> metis_tac[]) >>
  first_assum (drule_then strip_assume_tac) >>
  gvs[] >> qexistsl [`g'`, `i`, `j`, `s`, `t`] >>
  fs[layout_canonical_block_witness_def, layout_paired_ordinary_def]
QED

Theorem layout_canonical_ordinary_ready[local]:
  layout_driver_indexed es ass k /\
  layout_aligned_entry D lo vs0 C C' q0 es qs qend k p tp /\
  k.lop_cursor = SUC m /\ k.lop_pending /\
  qn = EL (SUC m) (q0::qs) ==>
  layout_canonical_entry D lo vs0 C C' q0 es qs ass qend qn (SUC m)
    (INL (k with lop_pending := F))
    (p with vs_inst_idx := SUC p.vs_inst_idx)
    (tp with vs_inst_idx := SUC tp.vs_inst_idx)
Proof
  strip_tac >> simp[layout_canonical_entry_def] >>
  fs[layout_aligned_entry_def] >>
  drule layout_ordinary_administrative >> strip_tac >>
  gvs[layout_canonical_ready_def, layout_aligned_entry_def,
      layout_ordinary_entry_def, layout_ordinary_trace_def,
      layout_phase_normalize_def, layout_phase_origin_def, layout_driver_indexed_def,
      concretizeLayoutCanonicalIndexTheory.layout_phase_canonical_def]
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

Theorem layout_canonical_ordinary_pending_reenter[local]:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t (INL g) /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  i.inst_opcode <> NOP /\ i.inst_opcode <> INVOKE /\
  j.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ~is_terminator j.inst_opcode /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  decoration_at fn i s q /\
  decoration_entry fn (p with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  finite_step C i s (OK p) /\ finite_step C' j t (OK tp) /\
  g.lop_cursor < LENGTH es /\ EL g.lop_cursor es = SOME (OriginOrdinary fuel p) /\
  k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\ k.lop_ids = g.lop_ids /\
  resolved_annotation_update g.lop_config (EL g.lop_cursor es)
    g.lop_ids g.lop_anns k.lop_anns /\
  resolved_annotation_edge C g.lop_cursor g.lop_config (EL g.lop_cursor es) qn
    g.lop_ids (EL g.lop_cursor ass) ids' (EL (SUC g.lop_cursor) ass) /\
  layout_phase_ok_abort D lo vs0 C C' q0 es qs qend
    (INL g) (INL k) (OK p) (OK tp) /\
  qn = EL (SUC g.lop_cursor) (q0::qs) ==>
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    qn (SUC n) bb (p with vs_inst_idx := SUC s.vs_inst_idx) bb'
    (tp with vs_inst_idx := SUC t.vs_inst_idx) (INL (k with lop_pending := F))
Proof
  strip_tac >>
  drule layout_canonical_ordinary_step_witness >> strip_tac >>
  `step_inst fuel C i s = OK p /\ step_inst_base j t = OK tp` by
    gvs[finite_step_iff, step_inst_non_invoke] >>
  drule_all layout_canonical_ordinary_success_witness >> strip_tac >>
  `layout_canonical_entry D lo vs0 C C' q0 es qs ass qend qn (SUC n)
    (INL (k with lop_pending := F))
    (p with vs_inst_idx := SUC p.vs_inst_idx)
    (tp with vs_inst_idx := SUC tp.vs_inst_idx)` by
    (irule layout_canonical_ordinary_ready >> metis_tac[]) >>
  `p.vs_current_bb = s.vs_current_bb /\ p.vs_inst_idx = s.vs_inst_idx /\
   tp.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[frameFiniteControlTheory.finite_step_nonterminator_control] >>
  irule layout_canonical_retained_reenter >>
  gvs[layout_phase_origin_def] >> metis_tac[]
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

(* The retained successor exposes the actual administrative target state.
   Observation refinements can therefore reuse the canonical witness proof. *)
Theorem layout_canonical_retained_next_witness:
  qs = MAP SND path /\ i.inst_opcode <> NOP /\
  decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  decorated_step C i s (OK post) q n ws qm ds /\
  ~is_terminator i.inst_opcode /\ decoration_consumes C i q post qm ev qn /\
  decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
    r qn (n+LENGTH ws+1) wb qe db /\
  selected_segment C q0 path n q (ws++[(ev,qn)]++wb) qe /\
  layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
  finite_step C' j t (OK v) /\ get_instruction bb' t.vs_inst_idx = SOME j /\
  layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend
    q n qm (n+LENGTH ws) i s j t (OK post) (OK v) ==>
  ~is_terminator j.inst_opcode /\
  (!a. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      q n bb s bb' t a ==>
    ?b. layout_phase_origin b = layout_phase_origin a /\ (ISL b ==> ISL a) /\
      layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
        qn (SUC (n+LENGTH ws)) bb (post with vs_inst_idx := SUC s.vs_inst_idx)
        bb' (v with vs_inst_idx := SUC t.vs_inst_idx) b)
Proof
  strip_tac >> gvs[] >>
  fs[layout_deferred_OS_def, layout_canonical_OS_def, layout_canonical_result_def] >>
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
  conj_tac
  >- (qhdtm_x_assum `layout_canonical_ES` mp_tac >>
      simp[layout_canonical_ES_def] >> strip_tac >>
      qhdtm_x_assum `layout_canonical_step_witness` mp_tac >>
      simp[layout_canonical_step_witness_def] >> strip_tac >>
      Cases_on `a` >> gvs[]
      >- simp[concretize_positions_nonterminator] >>
      fs[layout_canonical_block_witness_def] >> gvs[] >>
      drule_all layout_canonical_corridor_instruction >> strip_tac >> gvs[]) >>
  rpt strip_tac >> irule layout_canonical_retained_successor >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  fs[] >> metis_tac[layout_canonical_block_witness_retained]
QED

Theorem layout_canonical_retained_next_execution:
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
            q n (ws++[(ev,qn)]++wb) qe bb s bb' t r /\
          (!k. step_inst k C' j t = rs' /\ exec_block k C' bb' tb = rb' ==>
            exec_block k C' bb' t = rb')))
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
  gen_tac >> strip_tac >> conj_tac
  >- (simp[selected_block_match_def] >> qexists `rb'` >> conj_tac
      >- (irule finite_step_block_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
      irule layout_canonical_block_outcome_transport >>
      goal_assum (drule_at Any) >> fs[ADD1] >> metis_tac[]) >>
  rpt strip_tac >> simp[Once exec_block_def]
QED

Theorem layout_canonical_nop_reenter:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t (INL a) /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode = NOP /\
  decoration_at fn i s q /\ decoration_entry fn sn qn /\
  sn.vs_current_bb = s.vs_current_bb /\
  sn.vs_inst_idx = SUC s.vs_inst_idx /\
  k.lop_origin = a.lop_origin /\ k.lop_cursor = SUC n /\ k.lop_config = qn /\ 
  k.lop_pending /\ layout_driver_indexed es ass k /\
  layout_aligned_entry D lo vs0 C C' q0 es qs qend k post t /\
  post.vs_inst_idx = s.vs_inst_idx /\
  sn = (post with vs_inst_idx := SUC s.vs_inst_idx) ==>
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    qn (SUC n) bb sn bb' t (INL (k with lop_pending := F))
Proof
  strip_tac >>
  drule_all layout_ordinary_stutter_administrative >> strip_tac >>
  fs[layout_canonical_block_witness_def, layout_paired_ordinary_def] >>
  Cases_on `q` >>
  gvs[frameFiniteJointDecorationTheory.decoration_entry_def,
      frameFiniteJointDecorationTheory.decoration_at_def] >>
  conj_tac
  >- fs[layout_driver_indexed_def,
        concretizeLayoutCanonicalIndexTheory.layout_phase_canonical_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[] >>
  drule_all concretizeLayoutBlockPairingTheory.layout_block_pair_advance >>
  simp[concretize_positions_nop]
QED

Theorem layout_canonical_nop_next_witness:
  o1_ctx_shape C /\ ~ctx_has_dalloca C /\
  layout_cut_safe D lo ncut vs0 C qend /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  i.inst_opcode = NOP /\ decoration_at fn i s q /\
  get_instruction bb s.vs_inst_idx = SOME i /\
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
      ?tb. tb = t /\ layout_canonical_EB D lo vs0 C C' q0 es qs ass qend qn
          (n+LENGTH ws+1) bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
        (!rb'. finite_block C' bb' tb rb' /\
          layout_canonical_OB D lo vs0 C C' q0 es qs ass qend qn
            (n+LENGTH ws+1) qe (n+LENGTH ws+1+LENGTH wb) bb
            (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb r rb' ==>
          layout_canonical_OB D lo vs0 C C' q0 es qs ass qend
            q n qe (n+LENGTH (ws++[(ev,qn)]++wb)) bb s bb' t r rb'))
Proof
  strip_tac >>
  `layout_base_lookahead C q0 path q n i s` by
    (irule concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_next >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `ws = [] /\ qm = q /\ step_inst_base i s = OK post` by
    (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frameFiniteJointDecorationTheory.decorated_step_cases] >>
     simp[] >> metis_tac[]) >>
  gvs[] >>
  `post = s` by gvs[step_inst_base_def] >> gvs[] >>
  rename1 `decoration_at fn i s q` >>
  `qn = EL (SUC n) (q0::MAP SND path)` by
    (fs[frameSelectedDecorationTheory.selected_segment_def] >>
     simp[EL_APPEND_EQN, EL_MAP]) >>
  `!a. layout_canonical_block_witness D lo vs0 C C' q0 (MAP FST path)
      (MAP SND path) ass qend q n bb s bb' t a ==>
    ?b. layout_phase_origin b = layout_phase_origin a /\ (ISL b ==> ISL a) /\
      layout_canonical_block_witness D lo vs0 C C' q0 (MAP FST path)
        (MAP SND path) ass qend qn (SUC n) bb
        (s with vs_inst_idx := SUC s.vs_inst_idx) bb' t b` by
    (rpt strip_tac >> Cases_on `a`
     >- (`layout_canonical_step_witness D lo vs0 C C' q0 (MAP FST path)
           (MAP SND path) ass qend q n i s i t (INL x)` by
           (drule_all layout_canonical_block_witness_step >> strip_tac >>
            fs[layout_canonical_step_witness_def] >> metis_tac[]) >>
         drule_at (Pat `layout_canonical_step_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`) layout_canonical_nop_success >>
         simp[] >> disch_then (qspecl_then [`path`, `ncut`, `fn`, `P`] mp_tac) >>
         simp[] >> strip_tac >>
         `k.lop_config = qn /\ k.lop_cursor = SUC n` by
           gvs[layout_canonical_block_witness_def, layout_paired_ordinary_def,
               layout_aligned_entry_def, layout_ordinary_entry_def,
               layout_ordinary_trace_def] >>
         qexists `INL (k with lop_pending := F)` >>
         simp[layout_phase_origin_def] >>
         irule layout_canonical_nop_reenter >> simp[] >>
         qexistsl [`x`, `fn`, `i`, `s`, `q`, `s`] >> gvs[]) >>
     fs[layout_canonical_block_witness_def, layout_corridor_entry_def,
        layout_phase_normalize_def, ranked_terminal_entry_def,
        ranked_terminal_corridor_def] >>
     Cases_on `y.ltp_remaining` >> gvs[is_terminator_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  `layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path)
     ass qend q n i s i t` by
    (drule_all layout_canonical_block_step_choice >> strip_tac >>
     `j = i` by
       (qhdtm_x_assum `layout_canonical_ES` mp_tac >>
        simp[layout_canonical_ES_def, layout_canonical_step_witness_def] >>
        strip_tac >> Cases_on `a` >> gvs[concretize_positions_unchanged] >>
        fs[layout_canonical_block_witness_def, layout_corridor_entry_def,
           layout_phase_normalize_def, ranked_terminal_entry_def,
           ranked_terminal_corridor_def] >>
        Cases_on `y.ltp_remaining` >> gvs[is_terminator_def] >>
        qpat_x_assum `!d. d < SUC _ ==> _` (qspec_then `0` mp_tac) >>
        simp[] >> metis_tac[]) >> gvs[]) >>
  qexists `i` >> simp[] >> gen_tac >> strip_tac >> conj_tac
  >- (fs[layout_canonical_EB_def, ADD1] >> metis_tac[]) >>
  rpt strip_tac >>
  irule layout_canonical_block_outcome_transport >>
  goal_assum (drule_at Any) >> fs[ADD1] >> metis_tac[]
QED

Theorem layout_canonical_nop_next_execution:
  o1_ctx_shape C /\ layout_cut_safe D lo ncut vs0 C qend /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  i.inst_opcode = NOP /\ decoration_at fn i s q /\
  get_instruction bb s.vs_inst_idx = SOME i /\
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
            q n (ws++[(ev,qn)]++wb) qe bb s bb' t r /\
          (!k. step_inst k C' j t = rs' /\ exec_block k C' bb' tb = rb' ==>
            exec_block k C' bb' t = rb')))
Proof
  strip_tac >>
  drule_all layout_canonical_nop_next_witness >> strip_tac >>
  qexists `j` >> gvs[] >> rpt strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qexists `t` >> simp[] >> rpt strip_tac >>
  simp[selected_block_match_def] >> qexists `rb'` >> simp[]
QED

Theorem layout_canonical_retained_next:
  qs = MAP SND path /\ i.inst_opcode <> NOP /\
  decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  decorated_step C i s (OK post) q n ws qm ds /\
  ~is_terminator i.inst_opcode /\ decoration_consumes C i q post qm ev qn /\
  decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  selected_segment C q0 path n q (ws++[(ev,qn)]) qn /\
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t ==>
  ?j. layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
    (!rs'. finite_step C' j t rs' /\
      events_OS C C'
        (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
        q n qm (n+LENGTH ws) i s j t (OK post) rs' ==>
      ?tb. layout_canonical_EB D lo vs0 C C' q0 es qs ass qend qn
          (n+LENGTH ws+1) bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
        block_advance bb' i j t rs' tb /\
        !r wb qe db rb'.
          decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
            r qn (n+LENGTH ws+1) wb qe db /\
          selected_segment C q0 path n q (ws++[(ev,qn)]++wb) qe /\
          finite_block C' bb' tb rb' /\
          events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend) qn
            (n+LENGTH ws+1) qe (n+LENGTH ws+1+LENGTH wb) bb
            (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb r rb' ==>
          selected_block_match C'
            (events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend))
            q n (ws++[(ev,qn)]++wb) qe bb s bb' t r)
Proof
  strip_tac >>
  `selected_segment C q0 path n q (ws ++ [(ev,qn)] ++ []) qn` by simp[] >>
  `layout_base_lookahead C q0 path q n i s` by
    (irule concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_next >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  `get_instruction bb' t.vs_inst_idx = SOME j` by metis_tac[] >>
  qexists `j` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `events_OS _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [events_OS_def]) >>
  Cases_on `rs'` >>
  gvs[layout_deferred_OS_def, layout_canonical_OS_def, layout_canonical_result_def] >>
  `joint_segment C q ws qm /\ joint_transition C qm ev qn` by
    metis_tac[frameFiniteJointDecorationTheory.decorated_execution_segment,
      frameFiniteJointDecorationTheory.decoration_consumes_def] >>
  `selected_segment C q0 path (n+LENGTH ws) qm [(ev,qn)] qn` by
    (irule (cj 2 frameSelectedDecorationTheory.selected_segment_parts) >>
     simp[frameFiniteJointDecorationTheory.joint_segment_def] >>
     metis_tac[]) >>
  `qn = EL (SUC (n + LENGTH ws)) (q0::MAP SND path)` by
    (qpat_x_assum `selected_segment C q0 path n q (ws ++ [(ev,qn)]) qn`
       (mp_then Any mp_tac frameSelectedDecorationTheory.selected_segment_indices) >>
     simp[ADD1] >> strip_tac >>
     `n + (LENGTH ws + 1) = SUC (n + LENGTH ws)` by decide_tac >>
     qpat_x_assum `EL (n + (LENGTH ws + 1)) _ = qn` mp_tac >>
     pop_assum SUBST1_TAC >> simp[]) >>
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
  qexists `v with vs_inst_idx := SUC t.vs_inst_idx` >> rpt conj_tac
  >- (simp[layout_canonical_EB_def, ADD1] >>
      fs[layout_canonical_EB_def, ADD1] >> metis_tac[])
  >- simp[block_advance_def] >>
  rpt strip_tac >>
  qpat_x_assum `events_OB _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [events_OB_def]) >>
  `block_events_agree C C' bb s bb' t r rb'` by
    (irule block_events_agree_next >> metis_tac[]) >>
  simp[selected_block_match_def] >> qexists `rb'` >> conj_tac
  >- (irule finite_step_block_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  rewrite_tac[events_OB_def] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule layout_canonical_block_outcome_transport >>
  goal_assum (drule_at Any) >> fs[ADD1] >> metis_tac[]
QED

Theorem layout_canonical_nop_next:
  o1_ctx_shape C /\ layout_cut_safe D lo ncut vs0 C qend /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  i.inst_opcode = NOP /\ decoration_at fn i s q /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  decorated_step C i s (OK post) q n ws qm ds /\
  ~is_terminator i.inst_opcode /\ decoration_consumes C i q post qm ev qn /\
  decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  selected_segment C q0 path n q (ws++[(ev,qn)]) qn /\
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t ==>
  ?j. layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
    (!rs'. finite_step C' j t rs' /\
      events_OS C C'
        (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
        q n qm (n+LENGTH ws) i s j t (OK post) rs' ==>
      ?tb. layout_canonical_EB D lo vs0 C C' q0 es qs ass qend qn
          (n+LENGTH ws+1) bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
        block_advance bb' i j t rs' tb /\
        !r wb qe db rb'.
          decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
            r qn (n+LENGTH ws+1) wb qe db /\
          selected_segment C q0 path n q (ws++[(ev,qn)]++wb) qe /\
          finite_block C' bb' tb rb' /\
          events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend) qn
            (n+LENGTH ws+1) qe (n+LENGTH ws+1+LENGTH wb) bb
            (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb r rb' ==>
          selected_block_match C'
            (events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend))
            q n (ws++[(ev,qn)]++wb) qe bb s bb' t r)
Proof
  strip_tac >>
  `selected_segment C q0 path n q (ws ++ [(ev,qn)] ++ []) qn` by simp[] >>
  `layout_base_lookahead C q0 path q n i s` by
    (irule concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_next >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `ws = [] /\ qm = q /\ step_inst_base i s = OK post` by
    (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frameFiniteJointDecorationTheory.decorated_step_cases] >>
     simp[] >> metis_tac[]) >>
  gvs[] >>
  `post = s` by gvs[step_inst_base_def] >> gvs[] >>
  rename1 `decoration_at fn i s q` >>
  `qn = EL (SUC n) (q0::MAP SND path)` by
    (fs[frameSelectedDecorationTheory.selected_segment_def] >>
     simp[EL_APPEND_EQN, EL_MAP]) >>
  `!a. layout_canonical_block_witness D lo vs0 C C' q0 (MAP FST path)
      (MAP SND path) ass qend q n bb s bb' t a ==>
    ?b. layout_phase_origin b = layout_phase_origin a /\ (ISL b ==> ISL a) /\
      layout_canonical_block_witness D lo vs0 C C' q0 (MAP FST path)
        (MAP SND path) ass qend qn (SUC n) bb
        (s with vs_inst_idx := SUC s.vs_inst_idx) bb' t b` by
    (rpt strip_tac >> Cases_on `a`
     >- (`layout_canonical_step_witness D lo vs0 C C' q0 (MAP FST path)
           (MAP SND path) ass qend q n i s i t (INL x)` by
           (drule_all layout_canonical_block_witness_step >> strip_tac >>
            fs[layout_canonical_step_witness_def] >> metis_tac[]) >>
         drule_at (Pat `layout_canonical_step_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`) layout_canonical_nop_success >>
         disch_then (drule_at (Pat `layout_cut_safe _ _ _ _ _ _`)) >>
         simp[] >> disch_then (qspecl_then [`path`, `fn`, `P`] mp_tac) >>
         simp[] >> strip_tac >>
         `k.lop_config = qn /\ k.lop_cursor = SUC n` by
           gvs[layout_canonical_block_witness_def, layout_paired_ordinary_def,
               layout_aligned_entry_def, layout_ordinary_entry_def,
               layout_ordinary_trace_def] >>
         qexists `INL (k with lop_pending := F)` >>
         simp[layout_phase_origin_def] >>
         irule layout_canonical_nop_reenter >> simp[] >>
         qexistsl [`x`, `fn`, `i`, `s`, `q`, `s`] >> gvs[]) >>
     fs[layout_canonical_block_witness_def, layout_corridor_entry_def,
        layout_phase_normalize_def, ranked_terminal_entry_def,
        ranked_terminal_corridor_def] >>
     Cases_on `y.ltp_remaining` >> gvs[is_terminator_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  `layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path)
     ass qend q n i s i t` by
    (drule_all layout_canonical_block_step_choice >> strip_tac >>
     `j = i` by
       (qhdtm_x_assum `layout_canonical_ES` mp_tac >>
        simp[layout_canonical_ES_def, layout_canonical_step_witness_def] >>
        strip_tac >> Cases_on `a` >> gvs[concretize_positions_unchanged] >>
        fs[layout_canonical_block_witness_def, layout_corridor_entry_def,
           layout_phase_normalize_def, ranked_terminal_entry_def,
           ranked_terminal_corridor_def] >>
        Cases_on `y.ltp_remaining` >> gvs[is_terminator_def] >>
        qpat_x_assum `!d. d < SUC _ ==> _` (qspec_then `0` mp_tac) >>
        simp[] >> metis_tac[]) >> gvs[]) >>
  qexists `i` >> simp[] >> rpt strip_tac >>
  qexists `t` >> rpt conj_tac
  >- (fs[layout_canonical_EB_def, ADD1] >> metis_tac[])
  >- simp[block_advance_def] >>
  rpt strip_tac >>
  qpat_x_assum `events_OB _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [events_OB_def]) >>
  `block_events_agree C C' bb s bb' t r rb'` by
    (irule block_events_agree_skip >> simp[] >>
     metis_tac[frameFiniteJointDecorationTheory.decorated_execution_erases]) >>
  simp[selected_block_match_def, events_OB_def] >> qexists `rb'` >> simp[] >>
  irule layout_canonical_block_outcome_transport >>
  goal_assum (drule_at Any) >> fs[ADD1] >> metis_tac[]
QED

Theorem layout_canonical_next_entry_certificate:
  o1_ctx_shape C /\ layout_cut_safe D lo ncut vs0 C qend /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_next_entry_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
Proof
  strip_tac >> pure_rewrite_tac[selected_next_entry_certificate_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i.inst_opcode = NOP`
  >- (drule_all layout_canonical_nop_next >> strip_tac >>
      qexists `j` >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >> first_x_assum drule_all >>
      strip_tac >> qexists `tb` >> simp[]) >>
  drule_all layout_canonical_retained_next >> strip_tac >>
  qexists `j` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> first_x_assum drule_all >>
  strip_tac >> qexists `tb` >> simp[]
QED

Theorem layout_canonical_next_certificate_fuel:
  o1_ctx_shape C /\ layout_cut_safe D lo ncut vs0 C qend /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_next_certificate_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
    (events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend))
Proof
  strip_tac >> pure_rewrite_tac[selected_next_certificate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  `joint_segment C q ws qm` by metis_tac[cj 1 decorated_execution_segment] >>
  `joint_segment C qn wb qe` by metis_tac[cj 2 decorated_execution_segment] >>
  `joint_segment C q (ws++[(ev,qn)]) qn` by
    (irule joint_segment_append >> fs[decoration_consumes_def] >>
     simp[joint_segment_def] >> metis_tac[]) >>
  `selected_segment C q0 path n q (ws++[(ev,qn)]) qn` by
    (drule_all selected_segment_parts >> simp[]) >>
  Cases_on `i.inst_opcode = NOP`
  >- (drule_all layout_canonical_nop_next >> strip_tac >>
      qexists `j` >> conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      qexists `tb` >> conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >>
      first_x_assum drule_all >> rewrite_tac[selected_block_match_def] >> strip_tac >>
      rename1 `finite_block C' bb' t result` >>
      `exec_block k C' bb' t = rb' /\ finite_block C' bb' t rb'` by
        (qpat_x_assum `block_advance _ _ _ _ _ _` mp_tac >>
         rewrite_tac[block_advance_def] >> strip_tac
         >- gvs[] >>
         gvs[] >> conj_tac >- simp[Once exec_block_def] >>
         irule finite_step_block_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
      `result = rb'` by metis_tac[finite_block_deterministic] >>
      gvs[selected_block_match_fuel_def]) >>
  drule_all layout_canonical_retained_next >> strip_tac >>
  qexists `j` >> conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists `tb` >> conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >>
  first_x_assum drule_all >> rewrite_tac[selected_block_match_def] >> strip_tac >>
  rename1 `finite_block C' bb' t result` >>
  `exec_block k C' bb' t = rb' /\ finite_block C' bb' t rb'` by
    (qpat_x_assum `block_advance _ _ _ _ _ _` mp_tac >>
     rewrite_tac[block_advance_def] >> strip_tac
     >- gvs[] >>
     gvs[] >> conj_tac >- simp[Once exec_block_def] >>
     irule finite_step_block_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `result = rb'` by metis_tac[finite_block_deterministic] >>
  gvs[selected_block_match_fuel_def]
QED


(* Companion entry certificate: semantic aliases are initialized at the real
   post-PHI entry, independently of the ordinary relocation certificate. *)
Theorem layout_canonical_prefix_initialize:
  MEM bb fn.fn_blocks /\ bb_well_formed bb /\
  bb' = clear_nops_block
    (block_map_transform (concretize_inst_with_positions positions) bb) /\
  s.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
  t.vs_inst_idx = phi_prefix_length bb'.bb_instructions /\
  ~a.lop_pending /\ a.lop_config = q /\ a.lop_cursor = n /\
  a.lop_origin.lbo_source = bb /\ a.lop_origin.lbo_target = bb' /\
  layout_aligned_entry D lo vs0 C C' q0 es qs qend a s t /\
  layout_driver_indexed es ass a /\ decoration_entry fn s q /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  MEM fn C.ctx_functions /\ layout_driver_row C' fn fn' positions ==>
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t (INL a) /\ layout_paired_prefix_alias bb s bb' t
Proof
  strip_tac >> conj_tac
  >- (simp[layout_canonical_block_witness_def] >>
      goal_assum (drule_at Any) >> simp[] >>
      irule layout_paired_ordinary_initialize >> metis_tac[]) >>
  irule layout_paired_prefix_alias_initialize >> simp[]
QED

Theorem layout_canonical_prefix_retained_successor:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t a /\ layout_paired_prefix_alias bb s bb' t /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> NOP /\
  ~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode /\
  decoration_at fn i s q /\
  decoration_entry fn (p with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  finite_step C i s (OK p) /\ finite_step C' j t (OK tp) /\
  get_instruction bb' t.vs_inst_idx = SOME j /\
  layout_canonical_success D lo vs0 C C' q0 es qs ass qend m
    (i.inst_opcode = INVOKE) a p tp /\ qn = EL (SUC m) (q0::qs) ==>
  ?b. layout_phase_origin b = layout_phase_origin a /\ (ISL b ==> ISL a) /\
    layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      qn (SUC m) bb (p with vs_inst_idx := SUC s.vs_inst_idx) bb'
      (tp with vs_inst_idx := SUC t.vs_inst_idx) b /\
    layout_paired_prefix_alias bb (p with vs_inst_idx := SUC s.vs_inst_idx)
      bb' (tp with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> drule_all layout_canonical_retained_successor >> strip_tac >>
  qexists `b` >> simp[] >>
  irule layout_paired_prefix_alias_retained >> metis_tac[]
QED

Theorem layout_canonical_prefix_nop_successor:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t (INL a) /\ layout_paired_prefix_alias bb s bb' t /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode = NOP /\
  decoration_at fn i s q /\ decoration_entry fn sn qn /\
  sn.vs_current_bb = s.vs_current_bb /\
  sn.vs_inst_idx = SUC s.vs_inst_idx /\
  k.lop_origin = a.lop_origin /\ k.lop_cursor = SUC n /\ k.lop_config = qn /\
  k.lop_pending /\ layout_driver_indexed es ass k /\
  layout_aligned_entry D lo vs0 C C' q0 es qs qend k post t /\
  post.vs_inst_idx = s.vs_inst_idx /\
  sn = (post with vs_inst_idx := SUC s.vs_inst_idx) /\
  finite_step C i s (OK post) ==>
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    qn (SUC n) bb sn bb' t (INL (k with lop_pending := F)) /\
  layout_paired_prefix_alias bb sn bb' t
Proof
  strip_tac >> conj_tac
  >- (irule layout_canonical_nop_reenter >> metis_tac[]) >>
  `post = s` by
    (gvs[finite_step_iff, step_inst_def, step_inst_base_def]) >>
  gvs[] >> irule layout_paired_prefix_alias_nop >> metis_tac[]
QED

Theorem layout_canonical_prefix_invoke_successor[local]:
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t (INL g) /\ layout_paired_prefix_alias bb s bb' t /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode = INVOKE /\
  ~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode /\
  decoration_at fn i s q /\
  decoration_entry fn (p with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  finite_step C i s (OK p) /\ finite_step C' j t (OK tp) /\
  get_instruction bb' t.vs_inst_idx = SOME j /\
  layout_canonical_success D lo vs0 C C' q0 es qs ass qend m T (INL g) p tp /\
  qn = EL (SUC m) (q0::qs) ==>
  ?b. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      qn (SUC m) bb (p with vs_inst_idx := SUC s.vs_inst_idx) bb'
      (tp with vs_inst_idx := SUC t.vs_inst_idx) (INL b) /\
    layout_paired_prefix_alias bb (p with vs_inst_idx := SUC s.vs_inst_idx)
      bb' (tp with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g)` by
    (irule layout_canonical_block_witness_retained >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `layout_canonical_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_canonical_success_def] >> strip_tac >> Cases_on `b` >> fs[] >>
  rename1 `layout_driver_indexed es ass k` >>
  `p.vs_current_bb = s.vs_current_bb /\ p.vs_inst_idx = s.vs_inst_idx /\
   tp.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[frameFiniteControlTheory.finite_step_nonterminator_control] >>
  `layout_canonical_entry D lo vs0 C C' q0 es qs ass qend qn (SUC m) (INL k)
    (p with vs_inst_idx := SUC s.vs_inst_idx)
    (tp with vs_inst_idx := SUC t.vs_inst_idx)` by
    gvs[layout_canonical_entry_def, layout_canonical_ready_def,
      layout_aligned_entry_def, layout_ordinary_entry_def, layout_ordinary_trace_def,
      layout_driver_indexed_def, concretizeLayoutCanonicalIndexTheory.layout_phase_canonical_def] >>
  qexists `k` >> conj_tac
  >- (irule layout_canonical_retained_reenter >>
      gvs[layout_phase_origin_def] >>
      qexistsl [`g`, `fn`, `i`, `j`, `n`, `q`, `s`, `t`] >> simp[]) >>
  irule layout_paired_prefix_alias_retained >> metis_tac[]
QED

Theorem layout_canonical_prefix_base_successor[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t (INL g) /\ layout_paired_prefix_alias bb s bb' t /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  get_instruction bb' t.vs_inst_idx = SOME j /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  i.inst_opcode <> NOP /\ i.inst_opcode <> INVOKE /\
  ~(i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s) /\
  ~is_terminator i.inst_opcode /\ finite_step C i s (OK post) /\
  finite_step C' j t (OK tp) /\ qn = EL (SUC n) (q0::qs) ==>
  ?b. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      qn (SUC n) bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb'
      (tp with vs_inst_idx := SUC t.vs_inst_idx) (INL b) /\
    layout_paired_prefix_alias bb (post with vs_inst_idx := SUC s.vs_inst_idx)
      bb' (tp with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g)` by
    (irule layout_canonical_block_witness_retained >> metis_tac[]) >>
  `step_inst_base i s = OK post` by gvs[finite_step_iff, step_inst_non_invoke] >>
  drule_all layout_canonical_base_nonterm_pending >> strip_tac >>
  `layout_cut_safe D lo (SUC (LENGTH vs0.vs_gas_readings)) vs0 C qend` by
    metis_tac[layout_cut_safe_whole_run] >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode` by
    (gvs[] >> metis_tac[concretize_positions_nonterminator,
       concretize_positions_not_invoke]) >>
  `tpost = tp` by gvs[finite_step_iff, step_inst_non_invoke] >> gvs[] >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >> simp[] >> strip_tac >>
  qexists `k with lop_pending := F` >> conj_tac
  >- (irule layout_canonical_ordinary_pending_reenter >> gvs[] >> metis_tac[]) >>
  irule layout_paired_prefix_alias_retained >> metis_tac[]
QED

Theorem layout_canonical_prefix_next_ordinary:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
  decorated_step C i s (OK post) q n ws qm ds /\
  ~is_terminator i.inst_opcode /\ decoration_consumes C i q post qm ev qn /\
  decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
  decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
    r qn (n+LENGTH ws+1) wb qe db /\
  selected_segment C q0 path n q (ws++[(ev,qn)]++wb) qe /\
  layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
    q n bb s bb' t (INL g) /\ layout_paired_prefix_alias bb s bb' t /\
  layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
  finite_step C' j t (OK tp) /\
  (i.inst_opcode <> NOP ==> get_instruction bb' t.vs_inst_idx = SOME j) /\
  layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend
    q n qm (n+LENGTH ws) i s j t (OK post) (OK tp) /\
  ~(i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s) ==>
  ?b tb. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      qn (n+LENGTH ws+1) bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb (INL b) /\
    layout_paired_prefix_alias bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
    tb = (if i.inst_opcode = NOP then t else tp with vs_inst_idx := SUC t.vs_inst_idx) /\
    (!fuel rb'. step_inst fuel C' j t = OK tp /\ exec_block fuel C' bb' tb = rb' ==>
      exec_block fuel C' bb' t = rb')
Proof
  strip_tac >>
  `layout_base_lookahead C q0 path q n i s` by
    (irule concretizeLayoutSelectedBaseInterfaceTheory.layout_base_lookahead_next >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `finite_step C i s (OK post)` by
    metis_tac[frameFiniteJointDecorationTheory.decorated_execution_erases] >>
  Cases_on `i.inst_opcode = NOP`
  >- suspend "nop" >>
  suspend "retained"
QED

Resume layout_canonical_prefix_next_ordinary[nop]:
  `ws = [] /\ qm = q /\ step_inst_base i s = OK post` by
    (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frameFiniteJointDecorationTheory.decorated_step_cases] >>
     simp[] >> metis_tac[]) >>
  `post = s` by gvs[step_inst_base_def] >> gvs[] >>
  rename1 `decoration_at fn i s q` >>
  `qn = EL (SUC n) (q0::MAP SND path)` by
    (fs[frameSelectedDecorationTheory.selected_segment_def] >>
     simp[EL_APPEND_EQN, EL_MAP]) >>
  `layout_canonical_step_witness D lo vs0 C C' q0 (MAP FST path)
    (MAP SND path) ass qend q n i s i t (INL g)` by
    (drule_all layout_canonical_block_witness_step >> strip_tac >>
     fs[layout_canonical_step_witness_def] >> metis_tac[]) >>
  drule_at (Pat `layout_canonical_step_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_canonical_nop_success >>
  simp[] >> disch_then (qspecl_then
    [`path`, `SUC (LENGTH vs0.vs_gas_readings)`, `fn`, `P`] mp_tac) >>
  impl_tac >- metis_tac[layout_cut_safe_whole_run] >> strip_tac >>
  `k.lop_config = qn /\ k.lop_cursor = SUC n` by
    gvs[layout_canonical_block_witness_def, layout_paired_ordinary_def,
      layout_aligned_entry_def, layout_ordinary_entry_def, layout_ordinary_trace_def] >>
  qexists `k with lop_pending := F` >> simp[] >>
  conj_tac
  >- (fs[GSYM ADD1] >> irule layout_canonical_nop_reenter >> gvs[] >> metis_tac[]) >>
  irule layout_paired_prefix_alias_nop >> metis_tac[]
QED

Resume layout_canonical_prefix_next_ordinary[retained]:
  `get_instruction bb' t.vs_inst_idx = SOME j` by simp[] >>
  drule_all layout_canonical_retained_next_witness >> strip_tac >>
  `joint_segment C q ws qm /\ joint_segment C qn wb qe /\
   joint_transition C qm ev qn` by
    metis_tac[frameFiniteJointDecorationTheory.decorated_execution_segment,
      frameFiniteJointDecorationTheory.decoration_consumes_def] >>
  `qn = EL (SUC (n+LENGTH ws)) (q0::qs)` by
    (fs[APPEND_ASSOC] >>
     drule_all (SRULE[APPEND_ASSOC] frameSelectedDecorationTheory.selected_segment_edge) >>
     strip_tac >> gvs[GSYM ADD_ASSOC, GSYM ADD1, ADD_CLAUSES]) >>
  `?b. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      qn (SUC (n+LENGTH ws)) bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb'
      (tp with vs_inst_idx := SUC t.vs_inst_idx) (INL b) /\
    layout_paired_prefix_alias bb (post with vs_inst_idx := SUC s.vs_inst_idx)
      bb' (tp with vs_inst_idx := SUC t.vs_inst_idx)` by
    (Cases_on `i.inst_opcode = INVOKE`
     >- suspend "invoke" >>
     `ws = [] /\ qm = q` by
       (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[Once frameFiniteJointDecorationTheory.decorated_step_cases] >> metis_tac[]) >>
     gvs[] >> irule layout_canonical_prefix_base_successor >>
     gvs[] >> metis_tac[]) >>
  qexistsl [`b`, `tp with vs_inst_idx := SUC t.vs_inst_idx`] >>
  gvs[GSYM ADD1, ADD_CLAUSES] >>
  rpt strip_tac >> simp[Once exec_block_def]
QED

Resume layout_canonical_prefix_next_ordinary[invoke]:
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g)` by
    (irule layout_canonical_block_witness_retained >> gvs[] >> metis_tac[]) >>
  drule_all layout_deferred_next_consume >> strip_tac >>
  irule layout_canonical_prefix_invoke_successor >>
  gvs[] >> metis_tac[]
QED

Finalise layout_canonical_prefix_next_ordinary

Theorem layout_returncopy_preserves_operand[local]:
  i.inst_opcode = RETURNDATACOPY /\ step_inst_base i s = OK post ==>
  eval_operand d post = eval_operand d s
Proof
  simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `d` >> simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED

Theorem layout_canonical_exempt_scalar_demand:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\ decoration_at fn i s q /\
  i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  i.inst_operands = [opd;ops;opn] /\
  layout_paired_prefix_alias g.lop_origin.lbo_source s g.lop_origin.lbo_target t /\
  revert_forward_pair g.lop_origin.lbo_source s.vs_inst_idx jidx /\
  get_instruction g.lop_origin.lbo_source jidx = SOME term /\
  term.inst_operands = [ptr_op;len] /\
  d = resolve_block_assigns
    (REVERSE (TAKE (jidx - SUC s.vs_inst_idx)
      (DROP (SUC s.vs_inst_idx) g.lop_origin.lbo_source.bb_instructions))) len /\
  step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost /\
    eval_operand d post = eval_operand d tpost
Proof
  strip_tac >>
  drule_all layout_canonical_exempt_returncopy_scalar_success >> strip_tac >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by gvs[concretize_positions_unchanged] >>
  qpat_x_assum `j = i` SUBST_ALL_TAC >>
  `same_after_assigns
     (REVERSE (TAKE s.vs_inst_idx g.lop_origin.lbo_source.bb_instructions)) opn d` by
    (fs[contextCodegenRelTheory.revert_forward_pair_def] >> gvs[]) >>
  `eval_operand opn s = eval_operand d s /\
   eval_operand opn t = eval_operand d t` by
    (irule layout_paired_prefix_alias_source_demand >> metis_tac[]) >>
  qexists `tpost` >> simp[] >>
  metis_tac[layout_returncopy_preserves_operand]
QED

Theorem layout_assign_suffix_length[local]:
  !mid bb s rev tail fuel C post ptr_op len.
    DROP s.vs_inst_idx bb.bb_instructions = mid ++ rev::tail /\
    EVERY inst_wf mid /\ EVERY (\i. i.inst_opcode = ASSIGN) mid /\
    rev.inst_opcode = REVERT /\ rev.inst_operands = [ptr_op;len] /\
    exec_block fuel C bb s = Abort Revert_abort post ==>
    ?sz. eval_operand (resolve_block_assigns (REVERSE mid) len) s = SOME sz /\
         LENGTH post.vs_returndata = w2n sz
Proof
  Induct_on `mid`
  >- (rpt strip_tac >>
      `get_instruction bb s.vs_inst_idx = SOME rev` by
        (gvs[get_instruction_def, DROP_EQ_CONS]) >>
      qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def, step_inst_non_invoke, step_inst_base_def,
        AllCaseEqs()] >> rpt strip_tac >>
      gvs[contextCodegenRelTheory.resolve_block_assigns_def,
        venomStateTheory.revert_state_def, venomStateTheory.set_returndata_def,
        venomStateTheory.read_memory_def]) >>
  rpt strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (gvs[get_instruction_def, DROP_EQ_CONS]) >>
  fs[EVERY_DEF] >>
  reverse (drule stepWriteFootprintForwardTheory.step_assign_cases >>
    disch_then (qspecl_then [`s`, `fuel`, `C`] strip_assume_tac))
  >- (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `step_inst fuel C h s = OK p` >>
  `exec_block fuel C bb (p with vs_inst_idx := SUC s.vs_inst_idx) =
     Abort Revert_abort post` by
    (qpat_x_assum `exec_block _ _ _ s = _` mp_tac >>
     simp[Once exec_block_def, is_terminator_def]) >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions = mid ++ rev::tail` by
    (gvs[DROP_EQ_CONS] >> simp[GSYM rich_listTheory.DROP_DROP, ADD1]) >>
  first_x_assum (qspecl_then [`bb`, `p with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `!op. eval_operand op p = eval_operand (resolve_block_assigns [h] op) s` by
    (gen_tac >> irule m2v_assign_resolve_eval >>
     simp[contextCodegenRelTheory.resolve_block_assigns_def] >> metis_tac[]) >>
  `EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1 /\
     LENGTH a.inst_operands = 1) (REVERSE mid)` by
    (fs[rich_listTheory.EVERY_REVERSE, EVERY_MEM, venomWfTheory.inst_wf_def] >> metis_tac[]) >>
  qexists `sz` >>
  simp[contextCodegenRelPropsTheory.resolve_block_assigns_copy_append] >>
  fs[instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem layout_filter_rank_drop[local]:
  !R P xs k.
  DROP (LENGTH (FILTER P (MAP R (TAKE k xs))))
    (FILTER P (MAP R xs)) = FILTER P (MAP R (DROP k xs))
Proof
  rpt gen_tac >> qid_spec_tac `k` >> Induct_on `xs` >> simp[] >>
  Cases_on `k` >> simp[] >> Cases_on `P (R h)` >> simp[]
QED

Theorem layout_block_pair_drop[local]:
  layout_block_pair positions bb bb' k k' ==>
  DROP k' bb'.bb_instructions =
    FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions positions) (DROP k bb.bb_instructions))
Proof
  simp[concretizeLayoutBlockPairingTheory.layout_block_pair_def,
    concretizeLayoutBlockPairingTheory.layout_filter_rank_def,
    clear_nops_block_def, passTransformTheory.block_map_transform_def,
    layout_filter_rank_drop]
QED

Theorem layout_forward_suffix[local]:
  revert_forward_pair bb k jidx /\ get_instruction bb jidx = SOME term ==>
  ?tail. DROP (SUC k) bb.bb_instructions =
    TAKE (jidx - SUC k) (DROP (SUC k) bb.bb_instructions) ++ term::tail /\
    EVERY (\i. i.inst_opcode = ASSIGN)
      (TAKE (jidx - SUC k) (DROP (SUC k) bb.bb_instructions)) /\
    term.inst_opcode = REVERT
Proof
  simp[contextCodegenRelTheory.revert_forward_pair_def] >> rpt strip_tac >>
  `jidx < LENGTH bb.bb_instructions /\ EL jidx bb.bb_instructions = term` by
    gvs[get_instruction_def] >>
  qexists `DROP (SUC jidx) bb.bb_instructions` >>
  conj_tac
  >- (mp_tac (Q.ISPECL [`jidx - SUC k`, `DROP (SUC k) bb.bb_instructions`]
        rich_listTheory.TAKE_DROP_SUC) >>
      simp[EL_DROP, rich_listTheory.DROP_DROP_T] >>
      `jidx - SUC k + SUC k = jidx /\
       SUC k + SUC (jidx - SUC k) = SUC jidx` by decide_tac >> simp[]) >>
  conj_tac
  >- (simp[EVERY_EL, EL_TAKE, EL_DROP] >> rpt strip_tac >>
      first_x_assum irule >> simp[get_instruction_def] >>
      qexists `n + SUC k` >> simp[] >> decide_tac) >>
  gvs[]
QED

Theorem layout_assign_suffix_image[local]:
  !mid positions. EVERY (\i. i.inst_opcode = ASSIGN) mid ==>
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions positions) mid) = mid
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[concretize_positions_unchanged]
QED

Theorem layout_block_pair_assign_suffix[local]:
  layout_block_pair positions bb bb' k k' /\
  DROP k bb.bb_instructions = mid ++ rev::tail /\
  EVERY (\i. i.inst_opcode = ASSIGN) mid /\ rev.inst_opcode = REVERT ==>
  ?tail'. DROP k' bb'.bb_instructions = mid ++ rev::tail'
Proof
  strip_tac >> drule layout_block_pair_drop >>
  simp[MAP_APPEND, FILTER_APPEND_DISTRIB, layout_assign_suffix_image,
    concretize_positions_unchanged] >> metis_tac[]
QED

Theorem layout_canonical_source_block_wf[local]:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions ==>
  EVERY inst_wf g.lop_origin.lbo_source.bb_instructions
Proof
  simp[layout_canonical_step_witness_def, layout_canonical_block_witness_def,
    layout_paired_ordinary_def] >> rpt strip_tac >> gvs[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM e (fn_insts fn)` by
    (irule fragExecTheory.lookup_block_fn_insts >> metis_tac[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem layout_forward_block_revert_empty:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\ decoration_at fn i s q /\
  i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  i.inst_operands = [opd;ops;opn] /\
  layout_paired_prefix_alias g.lop_origin.lbo_source s g.lop_origin.lbo_target t /\
  revert_forward_pair g.lop_origin.lbo_source s.vs_inst_idx jidx /\
  get_instruction g.lop_origin.lbo_source jidx = SOME term /\
  term.inst_operands = [ptr_op;len] /\ step_inst_base i s = OK post /\
  exec_block fuel C g.lop_origin.lbo_source s = Abort Revert_abort fin /\
  fin.vs_returndata = [] /\
  exec_block tfuel C' g.lop_origin.lbo_target t = Abort Revert_abort tfin ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost /\
    tfin.vs_returndata = []
Proof
  strip_tac >>
  qabbrev_tac `mid = TAKE (jidx - SUC s.vs_inst_idx)
    (DROP (SUC s.vs_inst_idx) g.lop_origin.lbo_source.bb_instructions)` >>
  `?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost /\
    eval_operand (resolve_block_assigns (REVERSE mid) len) post =
    eval_operand (resolve_block_assigns (REVERSE mid) len) tpost` by
    (irule layout_canonical_exempt_scalar_demand >> simp[Abbr `mid`] >> metis_tac[]) >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by gvs[concretize_positions_unchanged] >> gvs[] >>
  drule_all layout_forward_suffix >> strip_tac >>
  `EVERY inst_wf mid` by
    (drule_all layout_canonical_source_block_wf >>
     simp[Abbr `mid`] >> metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
  `get_instruction g.lop_origin.lbo_target t.vs_inst_idx = SOME i` by
    (drule_all concretizeLayoutBlockPairingTheory.layout_block_pair_lookup >>
     simp[concretize_positions_unchanged]) >>
  `exec_block fuel C g.lop_origin.lbo_source
     (post with vs_inst_idx := SUC s.vs_inst_idx) = Abort Revert_abort fin` by
    (qpat_x_assum `exec_block fuel _ _ s = _` mp_tac >>
     simp[Once exec_block_def, step_inst_non_invoke, is_terminator_def]) >>
  `exec_block tfuel C' g.lop_origin.lbo_target
     (tpost with vs_inst_idx := SUC t.vs_inst_idx) = Abort Revert_abort tfin` by
    (qpat_x_assum `exec_block tfuel _ _ t = _` mp_tac >>
     simp[Once exec_block_def, step_inst_non_invoke, is_terminator_def]) >>
  drule_all concretizeLayoutBlockPairingTheory.layout_block_pair_advance >>
  simp[concretize_positions_unchanged] >> strip_tac >>
  `?tail'. DROP (SUC t.vs_inst_idx) g.lop_origin.lbo_target.bb_instructions = mid ++ term::tail'` by
    (irule layout_block_pair_assign_suffix >> fs[Abbr `mid`, ADD1] >> metis_tac[]) >>
  `?sz. eval_operand (resolve_block_assigns (REVERSE mid) len) post = SOME sz /\
        LENGTH fin.vs_returndata = w2n sz` by
    (qpat_assum `exec_block fuel _ _ (_ with vs_inst_idx := _) = _`
       (mp_then Any mp_tac layout_assign_suffix_length) >>
     simp[NoAsms, instIdxIndepTheory.eval_op_inst_idx] >>
     fs[Abbr `mid`] >> metis_tac[]) >>
  `?tsz. eval_operand (resolve_block_assigns (REVERSE mid) len) tpost = SOME tsz /\
         LENGTH tfin.vs_returndata = w2n tsz` by
    (qpat_assum `exec_block tfuel _ _ (_ with vs_inst_idx := _) = _`
       (mp_then Any mp_tac layout_assign_suffix_length) >>
     simp[NoAsms, instIdxIndepTheory.eval_op_inst_idx] >>
     fs[Abbr `mid`] >> metis_tac[]) >>
  gvs[]
QED

val _ = export_theory();
