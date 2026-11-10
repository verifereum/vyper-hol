Theory loadElimOccurrenceIntervals
Ancestors
  loadElimOccurrence loadElimOccurrenceCoverage loadElimOccurrencePositions
  venomExecProps venomExecProofs venomInstProps venomWf list rich_list
  loadElimExitCurrentness loadElimOccurrenceInversion

Theorem le_occ_interval_route:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  wf_function fn /\ fn_inst_wf fn ==>
  !pre e suffix. es = pre ++ e::suffix ==>
    is_fn_path fn ((le_occ_pre e).vs_current_bb :: le_occ_route suffix) /\
    LAST ((le_occ_pre e).vs_current_bb :: le_occ_route suffix) = s.vs_current_bb
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `pre` >> simp[] >> strip_tac >> gvs[] >>
      drule eval_phis_preserves_current_bb >>
      simp[le_occ_pre_def, le_occ_route_def, is_fn_path_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
      simp[APPEND_EQ_APPEND] >> strip_tac
      >- (Cases_on `l` >> gvs[]
          >- (drule step_preserves_control_flow >>
              simp[le_occ_pre_def, is_fn_path_def, le_occ_route_def]) >>
          first_x_assum (qspecl_then [`pre`, `e`, `t`] mp_tac) >>
          simp[] >> strip_tac >>
          `u.vs_current_bb = s.vs_current_bb` by
            metis_tac[step_preserves_control_flow] >>
          simp[le_occ_route_append, le_occ_route_def]) >>
      Cases_on `l` >> gvs[] >>
      drule step_preserves_control_flow >> simp[le_occ_pre_def, is_fn_path_def,
        le_occ_route_def]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  `fn_cfg_edge fn s.vs_current_bb u.vs_current_bb` by
    metis_tac[le_active_terminator_edge, lookup_block_label] >>
  `next.bb_label = u.vs_current_bb /\ p.vs_current_bb = u.vs_current_bb` by
    metis_tac[lookup_block_label, eval_phis_preserves_current_bb] >>
  simp[APPEND_EQ_APPEND] >> strip_tac
  >- (Cases_on `l` >> gvs[]
      >- simp[le_occ_pre_def, le_occ_route_def, is_fn_path_def] >>
      first_x_assum (qspecl_then [`pre`, `e`, `t`] mp_tac) >>
      simp[] >> strip_tac >>
      simp[le_occ_route_append, le_occ_route_def] >>
      pure_rewrite_tac[GSYM SNOC_APPEND, GSYM SNOC_CONS] >>
      conj_tac >- (rewrite_tac[SNOC_APPEND] >> irule is_fn_path_snoc >> simp[]) >>
      pure_rewrite_tac[LAST_SNOC] >> simp[]) >>
  Cases_on `l` >> gvs[]
  >- simp[le_occ_pre_def, le_occ_route_def, is_fn_path_def] >>
  Cases_on `t` >> gvs[] >>
  simp[le_occ_pre_def, le_occ_route_def, is_fn_path_def]
QED

(* Coverage after the selected event, never in its discarded prefix. *)
Theorem le_occ_interval_initial_coverage:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  wf_function fn /\ fn_inst_wf fn ==>
  !pre e suffix bb j v.
    es = pre ++ e::suffix /\
    lookup_block (le_occ_pre e).vs_current_bb fn.fn_blocks = SOME bb /\
    (case e of StepOcc eb n fuel u t => n < j
             | PhiOcc eb u p => phi_prefix_length bb.bb_instructions <= j) /\
    j < LENGTH bb.bb_instructions /\
    (le_occ_route suffix = [] ==> j < s.vs_inst_idx) /\
    MEM v (EL j bb.bb_instructions).inst_outputs ==>
    le_occ_wrote suffix v
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `pre` >> simp[] >> strip_tac >>
      gvs[le_occ_pre_def, le_occ_route_def, le_occ_wrote_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
      simp[APPEND_EQ_APPEND] >> strip_tac
      >- (Cases_on `l` >> gvs[]
          >- (gvs[le_occ_route_def] >> decide_tac) >>
          Cases_on `le_occ_route t = [] /\ ~(j < s.vs_inst_idx)`
          >- (`(le_occ_pre e).vs_current_bb = s.vs_current_bb` by
                (drule le_occ_interval_route >> simp[] >>
                 disch_then (qspecl_then [`pre`, `e`, `t`] mp_tac) >>
                 gvs[le_occ_route_def]) >>
              gvs[le_occ_route_append, le_occ_route_def] >>
              `j = s.vs_inst_idx` by decide_tac >>
              gvs[le_occ_wrote_def, le_occ_writes_def]) >>
          metis_tac[]) >>
      Cases_on `l` >> gvs[] >>
      gvs[le_occ_route_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
  `active_inst fn (EL s.vs_inst_idx bb.bb_instructions) s` by
    metis_tac[le_occ_prefix_active] >>
  `SUC s.vs_inst_idx = LENGTH bb.bb_instructions` by
    (gvs[] >> drule_all le_active_terminator_end >> strip_tac >> gvs[]) >>
  simp[APPEND_EQ_APPEND] >> strip_tac
  >- (Cases_on `l` >> gvs[]
      >- (gvs[le_occ_pre_def, le_occ_route_def] >> decide_tac) >>
      Cases_on `le_occ_route t = [] /\ ~(j < s.vs_inst_idx)`
      >- (`(le_occ_pre e).vs_current_bb = s.vs_current_bb` by
            (drule le_occ_interval_route >> simp[] >>
             disch_then (qspecl_then [`pre`, `e`, `t`] mp_tac) >>
             gvs[le_occ_route_def]) >>
          gvs[] >> `j = s.vs_inst_idx` by decide_tac >> gvs[] >>
          simp[le_occ_wrote_def] >> disj2_tac >>
          qexists_tac `StepOcc bb s.vs_inst_idx k s u` >>
          simp[le_occ_writes_def]) >>
      metis_tac[]) >>
  Cases_on `l` >> gvs[]
  >- gvs[le_occ_pre_def] >>
  Cases_on `t` >> gvs[le_occ_pre_def, le_occ_route_def] >>
  metis_tac[eval_phis_preserves_current_bb]
QED

(* A later visit includes the selected PHI batch itself.  The tail coverage
   theorem handles body instructions, even when that visit is re-entered. *)
Theorem le_occ_interval_phi_coverage:
  wf_function fn /\ fn_inst_wf fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  j < LENGTH bb.bb_instructions /\
  (le_occ_route suffix = [] ==> j < s.vs_inst_idx) /\
  MEM v (EL j bb.bb_instructions).inst_outputs ==>
  le_occ_wrote (PhiOcc bb u p :: suffix) v
Proof
  rpt strip_tac >>
  Cases_on `j < phi_prefix_length bb.bb_instructions`
  >- (simp[le_occ_wrote_def] >> qexists_tac `PhiOcc bb u p` >>
      simp[le_occ_writes_def] >> irule le_phi_prefix_outputs >> qexists_tac `j` >> simp[]) >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[le_occ_prefix_phi_semantics] >>
  `le_occ_wrote suffix v` by
    (drule le_occ_interval_initial_coverage >> simp[] >>
     disch_then irule >>
     qexistsl_tac [`bb`, `PhiOcc bb u p`, `j`, `pre`] >>
     simp[le_occ_pre_def]) >>
  gvs[le_occ_wrote_def] >> metis_tac[]
QED

Theorem le_occ_interval_later_phi_coverage:
  wf_function fn /\ fn_inst_wf fn /\
  le_occ_prefix C fn s0
    (pre ++ e :: (middle ++ PhiOcc bb u p :: tail)) i s /\
  j < LENGTH bb.bb_instructions /\
  (le_occ_route tail = [] ==> j < s.vs_inst_idx) /\
  MEM v (EL j bb.bb_instructions).inst_outputs ==>
  le_occ_wrote (middle ++ PhiOcc bb u p :: tail) v
Proof
  rpt strip_tac >>
  `le_occ_prefix C fn s0 ((pre ++ e::middle) ++ PhiOcc bb u p :: tail) i s` by
    (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]) >>
  drule_all le_occ_interval_phi_coverage >>
  simp[]
QED
