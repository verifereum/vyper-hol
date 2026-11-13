Theory concretizeLayoutRequestBlock
Ancestors concretizeLayoutRequestRelations concretizeLayoutCanonicalBlock
  concretizeLayoutCanonicalDriver concretizeLayoutCanonicalDeferred
  frameSelectedSimulation frameFiniteExecution frameFiniteJointDecoration
  concretizeLayoutSelectedBaseInterface venomExecSemantics venomInst list arithmetic

(* Exit certificates keep the exact recursive outcome endpoints. *)
Theorem layout_request_block_exit_certificate:
  selected_block_exit_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
Proof
  rw[selected_block_exit_certificate_def, layout_request_EB_def] >>
  `layout_base_lookahead C q0 path q n i s` by
    (drule_all layout_base_lookahead_exit >> simp[]) >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> simp[layout_request_ES_def] >> rpt strip_tac >>
  fs[layout_request_OS_def] >>
  `i.inst_opcode <> NOP` by
    (strip_tac >> qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once decorated_step_cases, step_inst_base_def] >> metis_tac[]) >>
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
  simp[layout_request_OB_def] >>
  Cases_on `r` >> Cases_on `rs'` >>
  gvs[layout_canonical_OB_def, layout_canonical_result_def]
QED

Theorem layout_request_term_certificate:
  selected_term_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
Proof
  rw[selected_term_certificate_def, layout_request_EB_def] >>
  `i.inst_opcode <> NOP /\ i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
  `layout_base_lookahead C q0 path q n i s` by
    simp[layout_base_lookahead_term] >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> simp[layout_request_ES_def] >> rpt strip_tac >>
  `w = [] /\ qe = q` by
    (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once decorated_step_cases] >> metis_tac[]) >>
  gvs[layout_request_OS_def, layout_deferred_OS_def, layout_canonical_OS_def] >>
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
  simp[layout_request_OB_def, layout_canonical_OB_def] >> rpt strip_tac >>
  `layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a'` by
    (irule layout_canonical_block_witness_retained >> simp[] >> metis_tac[]) >>
  first_assum (drule_then strip_assume_tac) >>
  gvs[] >> qexistsl [`g'`, `i`, `j`, `s`, `t`] >>
  fs[layout_canonical_block_witness_def,
     concretizeLayoutPairedEntryTheory.layout_paired_ordinary_def]
QED

Theorem layout_request_next_certificate:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_next_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> pure_rewrite_tac[selected_next_certificate_def] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `layout_request_EB` mp_tac >>
  pure_rewrite_tac[layout_request_EB_def] >> strip_tac >>
  Cases_on `i.inst_opcode = NOP`
  >- suspend "nop"
  >> suspend "retained"
QED

Resume layout_request_next_certificate[nop]:
  drule_all layout_canonical_nop_next_witness >> strip_tac >>
  qexists `j` >> simp[layout_request_ES_def] >> rpt strip_tac >>
  fs[layout_request_OS_def] >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `post = s` by
    (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once decorated_step_cases, step_inst_base_def] >> metis_tac[]) >>
  qexists `t` >> conj_tac
  >- (simp[layout_request_EB_def] >> fs[layout_request_state_def]) >>
  rpt strip_tac >> fs[layout_request_OB_def] >>
  simp[selected_block_match_def] >> qexists `rb'` >> simp[layout_request_OB_def] >>
  gvs[]
QED

Resume layout_request_next_certificate[retained]:
  `layout_base_lookahead C q0 path q n i s` by
    (irule layout_base_lookahead_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all layout_canonical_block_step_choice >> strip_tac >>
  qexists `j` >> simp[layout_request_ES_def] >> rpt strip_tac >>
  fs[layout_request_OS_def] >>
  `?v. rs' = OK v` by
    (Cases_on `rs'` >>
     gvs[layout_deferred_OS_def, layout_canonical_OS_def, layout_canonical_result_def]) >>
  gvs[] >>
  `get_instruction bb' t.vs_inst_idx = SOME j` by metis_tac[] >>
  drule_at (Pat `layout_deferred_OS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_canonical_retained_next_witness >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexists `v with vs_inst_idx := SUC t.vs_inst_idx` >> conj_tac
  >- (simp[layout_request_EB_def] >> conj_tac
      >- (simp[layout_canonical_EB_def, ADD1] >>
          fs[layout_canonical_EB_def, ADD1] >> metis_tac[]) >>
      fs[layout_request_state_def]) >>
  rpt strip_tac >> fs[layout_request_OB_def] >>
  simp[selected_block_match_def] >> qexists `rb'` >> conj_tac
  >- (irule finite_step_block_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[layout_request_OB_def] >> irule layout_canonical_block_outcome_transport >>
  goal_assum (drule_at Any) >> fs[ADD1] >> metis_tac[]
QED

Finalise layout_request_next_certificate

val _ = export_theory();
