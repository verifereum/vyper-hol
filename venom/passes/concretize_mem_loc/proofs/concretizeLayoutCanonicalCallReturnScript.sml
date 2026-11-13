Theory concretizeLayoutCanonicalCallReturn
Ancestors concretizeLayoutCanonicalCallEntry concretizeLayoutCanonicalDeferred
  concretizeLayoutCanonicalResume concretizeLayoutCanonicalDriver
  concretizeLayoutCallResult concretizeLayoutPhaseOrigin concretizeLayoutAlignedControl
  concretizeLayoutPairedEntry frameRelocationLocal frameDecoratedEndpoints
  frameSelectedSimulation frameFiniteExecution frameFiniteJointDecoration
  frameSelectedDecoration frameJointTransition frameControlAgreement
  venomExecSemantics list arithmetic

Theorem layout_canonical_caller_bind:
  layout_ordinary_entry D lo vs0 C C' q0 es qs qend a s t /\
  layout_ret_endpoint D lo vs0 C C' q0 es qs qend b sc tc ret ret' /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s sc)) = SOME post ==>
  ?post'. bind_outputs outs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state t tc)) = SOME post'
Proof
  strip_tac >> Cases_on `a.lop_config` >>
  gvs[layout_ordinary_entry_def, layout_ordinary_state_def] >>
  fs[local_rel_def] >>
  drule_all layout_ret_endpoint_bind_values >> metis_tac[]
QED

Theorem layout_invoke_paired_witness[local]:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend q n i s j t a /\
  i.inst_opcode = INVOKE ==>
  ?g bb bb' positions. a = INL g /\ layout_driver_indexed es ass g /\
    layout_paired_ordinary D lo vs0 C C' q0 es qs qend positions
      q n bb s bb' t g /\ get_instruction bb s.vs_inst_idx = SOME i
Proof
  Cases_on `a`
  >- (simp[layout_canonical_step_witness_def, layout_canonical_block_witness_def] >>
      metis_tac[]) >>
  rpt strip_tac >>
  gvs[layout_canonical_step_witness_def, layout_canonical_block_witness_def,
      concretizeLayoutPhaseCorridorTheory.layout_corridor_entry_def,
      frameRankedTerminalCorridorTheory.ranked_terminal_entry_def,
      layout_phase_normalize_def] >>
  Cases_on `y.ltp_remaining`
  >- gvs[frameRankedTerminalCorridorTheory.ranked_terminal_corridor_def] >>
  fs[frameRankedTerminalCorridorTheory.ranked_terminal_corridor_def] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem layout_canonical_return_deferred:
  es = MAP FST path /\ qs = MAP SND path /\
  decoration_at caller i s q /\ i.inst_opcode = INVOKE /\
  decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
  vs0.vs_allocas = FEMPTY /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  joint_transition C q NONE qc /\
  decorated_run C fn cs (IntRet ret send) qc (n+1) wc qe dc /\
  selected_segment C q0 path n q ((NONE,qc)::wc) qe /\
  layout_driver_indexed es ass phase /\ ~phase.lop_pending /\
  phase.lop_config = q /\ phase.lop_cursor = n /\
  layout_ordinary_entry D lo vs0 C C' q0 es qs qend phase s t /\
  layout_canonical_ret D lo vs0 C C' q0 es qs ass qend qe
    (n+1+LENGTH wc) ret send ret' tend /\
  bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s send)) = SOME post /\
  bind_outputs i.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state t tend)) = SOME post' ==>
  layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n qe
    (n+LENGTH ((NONE,qc)::wc)) i s j t (OK post) (OK post')
Proof
  strip_tac >> gvs[layout_canonical_ret_def] >>
  simp[layout_deferred_OS_def] >> rpt strip_tac >>
  drule_all layout_invoke_paired_witness >> strip_tac >> gvs[] >>
  `?stk PG G tn callee inst oms om hs h.
     b.lop_config = JointConfig stk PG G tn callee inst send oms om hs h /\
     inst.inst_opcode = RET` by fs[layout_ret_endpoint_def] >>
  `local_pending C b.lop_config (IntRet ret send) /\
   decoration_frame b.lop_config = decoration_frame qc` by
    (drule (cj 3 decorated_execution_intret_endpoint) >> simp[]) >>
  `callee = fn` by
    (Cases_on `phase.lop_config` >> Cases_on `qc` >>
     gvs[decoration_at_def, joint_transition_call_iff, decoration_frame_def]) >>
  drule_all layout_deferred_resume_event >> strip_tac >>
  `g.lop_config = phase.lop_config /\ g.lop_cursor = phase.lop_cursor` by
    fs[layout_paired_ordinary_def] >>
  `?birth ids rp rv anns. g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns` by
    (Cases_on `phase.lop_config` >>
     fs[layout_paired_ordinary_def, layout_aligned_entry_def,
        layout_ordinary_entry_def, layout_ordinary_state_def] >> metis_tac[]) >>
  Cases_on `phase.lop_config` >> gvs[decoration_at_def] >>
  `b.lop_cursor = SUC g.lop_cursor + LENGTH wc /\
   b.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  drule layout_canonical_resume_paired >> simp[GSYM ADD1] >>
  disch_then (drule_at (Pat `layout_ret_endpoint _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[GSYM ADD1] >>
  disch_then (drule_at (Pat `selected_segment _ _ _ _ _ _ _`)) >>
  simp[GSYM ADD1] >>
  disch_then (drule_at (Pat `layout_driver_indexed _ _ g`)) >>
  rule_assum_tac (REWRITE_RULE [GSYM ADD1, ADD_CLAUSES]) >>
  simp[ADD_CLAUSES] >> disch_then drule_all >>
  strip_tac >> irule layout_canonical_resume_success >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem layout_canonical_call_return_certificate:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_discipline lo C vs0 /\ vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_call_return_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_call_return_certificate_def] >>
  rpt gen_tac >> strip_tac >>
  `joint_segment C qc wc qe` by metis_tac[cj 3 decorated_execution_segment] >>
  drule_all layout_canonical_call_entry >> strip_tac >> gvs[] >>
  qexistsl [`out`, `ct`] >> conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on `rc'` >>
  gvs[layout_canonical_OutR_def, layout_canonical_result_def] >>
  rename1 `layout_canonical_ret _ _ _ _ _ _ _ _ _ _ _ _ ret send ret' tend` >>
  `?b. layout_ret_endpoint D lo vs0 C C' q0 (MAP FST path) (MAP SND path)
      qend b send tend ret ret'` by
    (fs[layout_canonical_ret_def] >> metis_tac[]) >>
  drule_all layout_canonical_caller_bind >> strip_tac >>
  simp[selected_step_match_def] >> qexists `OK post'` >>
  conj_tac
  >- (irule finite_step_invoke_return >> simp[] >> metis_tac[]) >>
  once_rewrite_tac[ADD_COMM] >>
  irule (PURE_REWRITE_RULE [LENGTH] layout_canonical_return_deferred) >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists `phase` >> simp[]) >>
  qexistsl [`dc`, `qc`, `ret`, `ret'`, `send`, `tend`] >> simp[]
QED

Theorem layout_canonical_call_return_certificate_fuel:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_discipline lo C vs0 /\ vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_call_return_certificate_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_call_return_certificate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  `joint_segment C qc wc qe` by metis_tac[cj 3 decorated_execution_segment] >>
  drule_all layout_canonical_call_entry >> strip_tac >> gvs[] >>
  qexistsl [`out`, `ct`] >> conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on `run_blocks k C' out ct` >>
  gvs[layout_canonical_OutR_def, layout_canonical_result_def, layout_canonical_ret_def] >>
  drule_all layout_canonical_caller_bind >> strip_tac >>
  rewrite_tac[selected_step_match_fuel_def] >> qexists `OK post'` >>
  conj_tac >- simp[Once step_inst_def] >>
  conj_tac
  >- (irule finite_step_invoke_return >> simp[] >> metis_tac[]) >>
  simp[layout_deferred_OS_def] >> rpt strip_tac >>
  drule_all layout_invoke_paired_witness >> strip_tac >> gvs[] >>
  `?stk PG G tn callee inst oms om hs h.
     b.lop_config = JointConfig stk PG G tn callee inst send oms om hs h /\
     inst.inst_opcode = RET` by fs[layout_ret_endpoint_def] >>
  `local_pending C b.lop_config (IntRet ret send) /\
   decoration_frame b.lop_config = decoration_frame qc` by
    (drule (cj 3 decorated_execution_intret_endpoint) >> simp[]) >>
  `callee = fn` by
    (Cases_on `phase.lop_config` >> Cases_on `qc` >>
     gvs[decoration_at_def, joint_transition_call_iff, decoration_frame_def]) >>
  drule_all layout_deferred_resume_event >> strip_tac >>
  `g.lop_config = phase.lop_config /\ g.lop_cursor = phase.lop_cursor` by
    fs[layout_paired_ordinary_def] >>
  `?birth ids rp rv anns. g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns` by
    (Cases_on `phase.lop_config` >>
     fs[layout_paired_ordinary_def, layout_aligned_entry_def,
        layout_ordinary_entry_def, layout_ordinary_state_def] >> metis_tac[]) >>
  Cases_on `phase.lop_config` >> gvs[decoration_at_def] >>
  `b.lop_cursor = SUC g.lop_cursor + LENGTH wc /\
   b.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  drule layout_canonical_resume_paired >> simp[GSYM ADD1] >>
  disch_then (drule_at (Pat `layout_ret_endpoint _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[GSYM ADD1] >>
  disch_then (drule_at (Pat `selected_segment _ _ _ _ _ _ _`)) >>
  simp[GSYM ADD1] >>
  disch_then (drule_at (Pat `layout_driver_indexed _ _ g`)) >>
  rule_assum_tac (REWRITE_RULE [GSYM ADD1, ADD_CLAUSES]) >>
  simp[ADD_CLAUSES] >> disch_then drule_all >>
  strip_tac >> irule layout_canonical_resume_success >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

val _ = export_theory();
