Theory concretizePtrExecutedDefinitions
Ancestors
  frameHistoryInstructions frameHistoryCfg frameExecutionHistory
  concretizeAnalysisPathDefinitions frameCfgBoundary contextCodegenRel
  venomInstProps venomExecProofs venomWf venomExecSemantics venomState venomInst
  list rich_list

Definition history_observations_def:
  history_observations fn h <=>
    !n. n < LENGTH h ==>
      history_instruction_prefix fn (TAKE (SUC n) h) /\
      active_inst fn (FST (EL n h)) (SND (EL n h))
End

Theorem history_observations_snoc[local]:
  history_observations fn h /\
  history_instruction_prefix fn (h ++ [(i,s)]) /\ active_inst fn i s ==>
  history_observations fn (h ++ [(i,s)])
Proof
  pure_rewrite_tac [history_observations_def] >> strip_tac >> gen_tac >> disch_tac >>
  Cases_on `n < LENGTH h`
  >- (`SUC n - LENGTH h = 0` by decide_tac >>
      simp[TAKE_APPEND, EL_APPEND1] >> metis_tac[])
  >> `n = LENGTH h` by (gvs[] >> decide_tac) >> gvs[TAKE_LENGTH_TOO_LONG, EL_APPEND2]
QED

Theorem frame_history_observations_invariant:
  !vs0 ctx stk PG G tn fn inst s hs h.
    frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    EVERY wf_function ctx.ctx_functions ==>
    MEM fn ctx.ctx_functions /\ history_instruction_prefix fn h /\
    h <> [] /\ LAST h = (inst,s) /\ history_observations fn h /\
    LIST_REL (\f h0. MEM f.cf_fn ctx.ctx_functions /\
      active_inst f.cf_fn f.cf_inst f.cf_state /\
      history_instruction_prefix f.cf_fn h0 /\ h0 <> [] /\
      LAST h0 = (f.cf_inst,f.cf_state) /\
      history_observations f.cf_fn h0) stk hs
Proof
  ho_match_mp_tac frame_history_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> disch_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_history_observations_invariant[entry]:
  rename1 `active_inst fn inst s1` >>
  drule lookup_function_MEM >> strip_tac >>
  `history_instruction_prefix fn [(inst,s1)]` by
    (irule history_instruction_prefix_entry >> simp[] >> metis_tac[EVERY_MEM]) >>
  simp[history_observations_def] >> rpt strip_tac >> gvs[]
QED

Resume frame_history_observations_invariant[next]:
  gvs[LAST_APPEND] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `history_instruction_prefix fn
    (h ++ [(inst',s' with vs_inst_idx := SUC s.vs_inst_idx)])` by
    (irule history_instruction_prefix_snoc >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_MEM]) >>
  simp[] >> irule history_observations_snoc >> simp[]
QED

Resume frame_history_observations_invariant[block]:
  gvs[LAST_APPEND] >> rename1 `active_inst fn inst' s1` >>
  `history_instruction_prefix fn (h ++ [(inst',s1)])` by
    (irule history_instruction_prefix_entry >> simp[LAST_APPEND] >>
     metis_tac[EVERY_MEM]) >>
  simp[] >> irule history_observations_snoc >> simp[]
QED

Resume frame_history_observations_invariant[call]:
  gvs[] >> drule lookup_function_MEM >> strip_tac >>
  rename1 `enters_block callee cs s1` >>
  rename1 `active_inst callee ci s1` >>
  `history_instruction_prefix callee [(ci,s1)]` by
    (irule history_instruction_prefix_entry >> simp[] >> metis_tac[EVERY_MEM]) >>
  simp[history_observations_def] >> rpt strip_tac >> gvs[]
QED

Resume frame_history_observations_invariant[ret]:
  gvs[LAST_APPEND] >> drule return_binding_current_bb >> strip_tac >>
  `history_instruction_prefix f.cf_fn
    (caller_h ++ [(inst',s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)])` by
    (irule history_instruction_prefix_snoc >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_MEM]) >>
  simp[] >> irule history_observations_snoc >> simp[]
QED

Finalise frame_history_observations_invariant

Theorem history_visits_completed_observation[local]:
  !h k. k < LENGTH (history_visits h) - 1 ==>
    ?n. n < LENGTH h - 1 /\
      is_terminator (FST (EL n h)).inst_opcode /\
      (SND (EL n h)).vs_current_bb = EL k (history_visits h)
Proof
  Induct >> simp[history_visits_def] >>
  qx_gen_tac `obs` >> PairCases_on `obs` >>
  namedCases_on `h` ["", "obs2 rest"]
  >- simp[history_visits_def] >>
  PairCases_on `obs2` >>
  Cases_on `is_terminator obs0.inst_opcode` >> simp[history_visits_def]
  >- (Cases_on `k` >> simp[]
      >- (strip_tac >> qexists_tac `0` >> simp[]) >>
      strip_tac >> first_x_assum (qspec_then `n` mp_tac) >>
      (impl_tac >- decide_tac) >>
      disch_then (qx_choose_then `m` strip_assume_tac) >>
      qexists_tac `SUC m` >> gvs[])
  >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `SUC n` >> gvs[]
QED

Theorem active_terminator_final_index[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  active_inst fn i s /\ is_terminator i.inst_opcode ==>
    s.vs_inst_idx = PRE (LENGTH bb.bb_instructions) /\
    i = EL s.vs_inst_idx bb.bb_instructions
Proof
  rpt strip_tac >> gvs[active_inst_def] >>
  `bb = bb'` by metis_tac[same_label_same_block] >> gvs[] >>
  gvs[wf_function_def, bb_well_formed_def] >> metis_tac[]
QED

Theorem frame_history_completed_visit_instructions:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\
  k < LENGTH (history_visits h) - 1 /\
  MEM bb fn.fn_blocks /\ bb.bb_label = EL k (history_visits h) /\
  phi_prefix_length bb.bb_instructions <= j /\ j < LENGTH bb.bb_instructions ==>
  ?old_inst old_s. MEM (old_inst,old_s) (FRONT h) /\
    old_s.vs_current_bb = bb.bb_label /\ old_s.vs_inst_idx = j /\
    active_inst fn old_inst old_s /\ old_inst = EL j bb.bb_instructions
Proof
  rpt strip_tac >>
  drule history_visits_completed_observation >> strip_tac >>
  drule frame_history_observations_invariant >> simp[] >> strip_tac >>
  `n < LENGTH h` by decide_tac >>
  `history_instruction_prefix fn (TAKE (SUC n) h) /\
   active_inst fn (FST (EL n h)) (SND (EL n h))` by
    gvs[history_observations_def] >>
  `wf_function fn` by metis_tac[EVERY_MEM] >>
  `bb.bb_label = (SND (EL n h)).vs_current_bb` by simp[] >>
  drule_all active_terminator_final_index >> strip_tac >>
  Cases_on `j = (SND (EL n h)).vs_inst_idx`
  >- suspend "final"
  >> suspend "earlier"
QED

Resume frame_history_completed_visit_instructions[final]:
  qexists_tac `SND (EL n h)` >> simp[] >>
  `MEM (EL n h) (FRONT h)` suffices_by metis_tac[pairTheory.PAIR] >>
  `n < LENGTH (FRONT h)` by simp[LENGTH_FRONT] >>
  `EL n h = EL n (FRONT h)` by
    (qpat_assum `h <> []` (mp_tac o MATCH_MP APPEND_FRONT_LAST) >>
     disch_then (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [GSYM th]) >>
     simp[EL_APPEND1]) >>
  metis_tac[MEM_EL]
QED

Resume frame_history_completed_visit_instructions[earlier]:
  `j < (SND (EL n h)).vs_inst_idx` by decide_tac >>
  `TAKE (SUC n) h <> [] /\ LAST (TAKE (SUC n) h) = EL n h` by
    simp[TAKE_SUC_BY_TAKE, LAST_SNOC] >>
  `?oi os. MEM (oi,os) (FRONT (TAKE (SUC n) h)) /\
    os.vs_current_bb = bb.bb_label /\ os.vs_inst_idx = j /\
    active_inst fn oi os /\ oi = EL j bb.bb_instructions` by
    (qpat_x_assum `history_instruction_prefix fn (TAKE (SUC n) h)` mp_tac >>
     simp[history_instruction_prefix_def] >>
     disch_then (qspecl_then [`FST (EL n h)`, `SND (EL n h)`, `bb`, `j`] mp_tac) >>
     simp[]) >>
  qexists_tac `os` >> gvs[] >>
  `TAKE (SUC n) h = TAKE (SUC n) (FRONT h)` by
    (qpat_assum `h <> []` (mp_tac o MATCH_MP APPEND_FRONT_LAST) >>
     disch_then (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [GSYM th]) >>
     `SUC n - LENGTH (FRONT h) = 0` by (simp[LENGTH_FRONT] >> decide_tac) >>
     simp[TAKE_APPEND]) >>
  `TAKE (SUC n) h <> []` by simp[TAKE_SUC_BY_TAKE] >>
  `MEM (EL os.vs_inst_idx bb.bb_instructions,os) (TAKE (SUC n) h)` by
    metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
  metis_tac[MEM_TAKE]
QED

Finalise frame_history_completed_visit_instructions
