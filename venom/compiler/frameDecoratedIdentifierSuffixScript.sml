Theory frameDecoratedIdentifierSuffix
Ancestors frameResolvedSegments frameFiniteJointDecoration frameDecoratedEndpoints
  frameFiniteExecution frameJointTransition frameSelectedDecoration
  frameActivationLifetime frameResolvedCoherent venomInst list arithmetic

Definition identifier_pending_def:
  identifier_pending i ids idse <=>
    if i.inst_opcode = INVOKE then ?fresh. idse = fresh::ids else idse = ids
End

Theorem identifier_consumes[local]:
  decoration_consumes C i q post qm ev qn /\
  identifier_pending i ids idsm /\
  resolved_annotation_edge C n qm ev qn idsm anns idse annse ==>
  idse = ids
Proof
  simp[decoration_consumes_def, identifier_pending_def,
       resolved_annotation_edge_def] >> rpt strip_tac >>
  gvs[lifetime_step_def]
QED

Theorem decorated_execution_identifiers:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    !ids anns idse annse.
    resolved_annotation_segment C n q w qe ids anns idse annse ==>
    (!post. r = OK post ==> identifier_pending i ids idse) /\
    (!ret send. r = IntRet ret send ==> idse = ids)) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    !ids anns idse annse.
    resolved_annotation_segment C n q w qe ids anns idse annse ==>
    ((?post. r = OK post) \/ (?ret send. r = IntRet ret send)) ==>
    idse = ids) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    !ids anns idse annse.
    resolved_annotation_segment C n q w qe ids anns idse annse ==>
    (!ret send. r = IntRet ret send ==> idse = ids))
Proof
  ho_match_mp_tac decorated_step_strongind >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[resolved_annotation_segment_def, identifier_pending_def])
  >- (rpt strip_tac >> gvs[resolved_annotation_segment_def] >>
      fs[resolved_annotation_edge_def, lifetime_step_def] >>
      fs[ADD1, identifier_pending_def] >> metis_tac[])
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      Cases_on `post.vs_halted` >> gvs[identifier_pending_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      drule (cj 1 decorated_execution_segment) >> strip_tac >>
      drule resolved_annotation_segment_append_at >>
      disch_then (fn th =>
        pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> pure_once_rewrite_tac[th]) >>
      simp[resolved_annotation_segment_def] >> rpt strip_tac >>
      `identifier_pending i ids idsm` by metis_tac[] >>
      `ids1 = ids` by metis_tac[identifier_consumes] >> gvs[] >>
      fs[ADD1] >> metis_tac[])
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      drule (cj 2 decorated_execution_segment) >> strip_tac >>
      drule resolved_annotation_segment_append_at >>
      disch_then (fn th =>
        pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> pure_once_rewrite_tac[th]) >>
      simp[resolved_annotation_segment_def] >> rpt strip_tac >>
      `idsm = ids` by metis_tac[] >> gvs[] >>
      fs[resolved_annotation_edge_def, lifetime_step_def, ADD1] >> metis_tac[])
  >- (rpt strip_tac >> gvs[])
  >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem decorated_run_IntRet_identifiers:
  decorated_run C fn cs (IntRet ret send) qc n w qe dc /\
  resolved_annotation_segment C n qc w qe ids anns idse annse ==>
  idse = ids
Proof
  strip_tac >> drule (cj 3 decorated_execution_identifiers) >>
  disch_then drule >> simp[]
QED

Theorem selected_run_IntRet_identifiers:
  selected_run C q0 path fn cs (IntRet ret send) qc n w qe dc /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path)) (EL k iss) (EL k ass)
      (EL (SUC k) iss) (EL (SUC k) ass)) ==>
  EL (n+LENGTH w) iss = EL n iss
Proof
  simp[selected_run_def] >> strip_tac >>
  drule_all (SRULE [] selected_resolved_annotation_segment) >>
  strip_tac >> gvs[] >>
  drule_all decorated_run_IntRet_identifiers >> simp[]
QED

val _ = export_theory();
