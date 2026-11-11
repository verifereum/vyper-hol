Theory frameDecoratedAnnotationSuffix
Ancestors frameResolvedSegments frameFiniteJointDecoration frameDecoratedEndpoints
  frameFiniteExecution frameJointTransition frameSelectedDecoration venomInst list arithmetic

Definition annotation_pending_suffix_def:
  annotation_pending_suffix i ann saved anns <=>
    if i.inst_opcode = INVOKE then ?callee. anns = callee::ann::saved
    else anns = ann::saved
End

Theorem annotation_consumes_suffix:
  decoration_consumes C i q post qm ev qn /\
  annotation_pending_suffix i ann saved anns /\
  resolved_annotation_edge C n qm ev qn ids anns ids' anns' ==>
  ?ann'. anns' = ann'::saved
Proof
  simp[decoration_consumes_def, annotation_pending_suffix_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[resolved_annotation_ordinary_suffix, resolved_annotation_resume_suffix]
QED

Theorem decorated_execution_annotation_suffix:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    !ids ann saved idse annse.
    resolved_annotation_segment C n q w qe ids (ann::saved) idse annse ==>
    (!post. r = OK post ==> annotation_pending_suffix i ann saved annse) /\
    (!ret send. r = IntRet ret send ==> annse = ann::saved)) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    !ids ann saved idse annse.
    resolved_annotation_segment C n q w qe ids (ann::saved) idse annse ==>
    ((?post. r = OK post) \/ (?ret send. r = IntRet ret send)) ==>
    ?ann'. annse = ann'::saved) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    !ids ann saved idse annse.
    resolved_annotation_segment C n q w qe ids (ann::saved) idse annse ==>
    (!ret send. r = IntRet ret send ==> ?ann'. annse = ann'::saved))
Proof
  ho_match_mp_tac decorated_step_strongind >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[resolved_annotation_segment_def, annotation_pending_suffix_def])
  >- (rpt strip_tac >> gvs[resolved_annotation_segment_def] >>
      drule resolved_annotation_call_suffix >> strip_tac >> gvs[] >>
      fs[ADD1, annotation_pending_suffix_def] >> metis_tac[])
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      Cases_on `post.vs_halted` >> gvs[annotation_pending_suffix_def] >>
      metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      drule (cj 1 decorated_execution_segment) >> strip_tac >>
      drule resolved_annotation_segment_append_at >>
      disch_then (fn th =>
        pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> pure_once_rewrite_tac[th]) >>
      simp[resolved_annotation_segment_def] >> rpt strip_tac >>
      `annotation_pending_suffix i ann saved annsm` by metis_tac[] >>
      drule_all annotation_consumes_suffix >> strip_tac >> gvs[] >>
      fs[ADD1] >> metis_tac[])
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      drule (cj 2 decorated_execution_segment) >> strip_tac >>
      drule resolved_annotation_segment_append_at >>
      disch_then (fn th =>
        pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> pure_once_rewrite_tac[th]) >>
      simp[resolved_annotation_segment_def] >> rpt strip_tac >>
      `?ann'. annsm = ann'::saved` by metis_tac[] >> gvs[] >>
      drule resolved_annotation_block_suffix >> strip_tac >> gvs[] >>
      fs[ADD1] >> metis_tac[])
  >- (rpt strip_tac >> gvs[])
  >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem decorated_run_IntRet_annotation_suffix:
  decorated_run C fn cs (IntRet ret send) qc n w qe dc /\
  resolved_annotation_segment C n qc w qe ids (callee::caller::saved) idse annse ==>
  ?callee'. annse = callee'::caller::saved
Proof
  strip_tac >> drule (cj 3 decorated_execution_annotation_suffix) >>
  disch_then drule >> simp[]
QED

Theorem selected_run_IntRet_annotation_suffix:
  selected_run C q0 path fn cs (IntRet ret send) qc n w qe dc /\
  EL n ass = callee::caller::saved /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path)) (EL k iss) (EL k ass)
      (EL (SUC k) iss) (EL (SUC k) ass)) ==>
  ?callee'. EL (n+LENGTH w) ass = callee'::caller::saved
Proof
  simp[selected_run_def] >> strip_tac >>
  drule_all (SRULE [] selected_resolved_annotation_segment) >>
  strip_tac >> gvs[] >>
  drule_all decorated_run_IntRet_annotation_suffix >> simp[]
QED
