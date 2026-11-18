Theory gasFocusFmpCutRestorePrefix
Ancestors
  gasFocusFmpStagePin gasFocusFmpCutSites lowerDloadPtrRawReachable
  fmpStageFmpStepsRestoreBounds fmpStageFmpStepsRestoreIdle
  fmpStageFmpStepsRestorePosition fmpStageFmpStepsRestoreCut
  fmpStageFmpStepsRestoreFrame fmpStageFmpStepsRestoreControl
  fmpStageFmpStepsLedgerSaved fmpStageFmpStepsLedgerRestrict
  fmpRestoreProps fmpStepAnalysis fmpStepStack fmpStageOpBase
  fmpStageRel o1PassContract contextCodegenRel venomExecProps
  venomInst venomWf venomState finite_map list rich_list words pair
  fmpStageFmpStepsLedgerPartition fmpStageFmpStepsRetSource
  gasFocusChronologicalCut concretizePtrChronologicalHistory

(* Saved callers lie inside the same cut. Their sites end no later than
   the source FMP saved by the innermost caller. *)
Theorem cut_restore_saved_bounds[local]:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s ==>
  !f. MEM f stk ==>
    (!v b z. FLOOKUP f.cf_prov v = SOME (b,z) /\ 0 < z ==>
       b + z <= fmp_frame_base (w2n vs.vs_fmp) stk) /\
    (!k b z. k < LENGTH f.cf_params /\ EL k f.cf_params = SOME (b,z) /\ 0 < z ==>
       b + z <= fmp_frame_base (w2n vs.vs_fmp) stk)
Proof
  strip_tac >>
  `EVERY (\f. gas_cut n vs f.cf_state) stk` by
    (drule ptr_reachable_has_chrono_history >> strip_tac >>
     drule ptr_chrono_saved_callers_cut >> simp[ptr_observe_def]) >>
  drule fmp_stage_saved_source >> strip_tac >>
  namedCases_on `stk` ["", "head tail"] >- simp[] >>
  `EVERY (\f. w2n f.cf_state.vs_fmp <= w2n head.cf_state.vs_fmp) tail` by
    (qpat_assum `!pre f rest. _` (qspecl_then [`[]`, `head`, `tail`] mp_tac) >>
     simp[NoAsms] >> strip_tac >>
     `gas_cut n vs head.cf_state` by fs[] >>
     irule (cj 3 focus_fmp_frame_sites_upto) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qx_gen_tac `f` >> disch_tac >>
  `w2n f.cf_state.vs_fmp <= w2n head.cf_state.vs_fmp` by
    (fs[EVERY_MEM] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `?pre rest. head::tail = pre ++ f::rest` by
    (pure_rewrite_tac [GSYM MEM_SPLIT] >> first_assum ACCEPT_TAC) >>
  qpat_assum `!pre f rest. _` (qspecl_then [`pre`, `f`, `rest`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `gas_cut n vs f.cf_state` by fs[EVERY_MEM] >>
  qpat_assum `frame_reachable vs C rest _ _ _ _ _ _`
    (mp_then Any mp_tac focus_fmp_frame_sites_upto) >>
  disch_then (qspecl_then [`w2n vs.vs_fmp`, `n`] mp_tac) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >> strip_tac >>
  simp[fmp_frame_base_def] >> conj_tac
  >- (rpt strip_tac >> qpat_assum `!v b z. _` drule >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `EVERY _ f.cf_params` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
  disch_then (qspec_then `k` mp_tac) >> simp[] >> decide_tac
QED

(* The restore belongs to the current source fetch, but is not itself a
   matching fetch. The source frame and both suspended stacks stay put. *)
Theorem focus_fmp_cut_restore_prefix:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  ssa_form fn /\ fn.fn_fmp_signature = NONE /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s /\ ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts ==>
  ?fn' bb bb' infos ctx runner i d u cut.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_stage_lowered infos ctx runner fn fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    i = t.vs_inst_idx /\
    i = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) s.vs_current_bb
          bb.bb_instructions s.vs_inst_idx /\
    i < LENGTH bb'.bb_instructions /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = i + d /\
    i + d <= LENGTH bb'.bb_instructions /\ cut <= lo /\
    (!fuel. fmp_target_run fuel C' fn.fn_name t d u) /\
    (case FLOOKUP (fmp_stage_plan infos ctx fn)
       (s.vs_current_bb,s.vs_inst_idx) of
       NONE => d = 0 /\ u = t /\ cut = lo
     | SOME target => d = 1 /\ ?id value.
         EL i bb'.bb_instructions = mk_inst id ASSIGN [Var target] [runner] /\
         lookup_var target t = SOME value /\
         u = (update_var runner value t) with vs_inst_idx := SUC i) /\
    fmp_stage_rel D C'
      (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut})
      fmp0 raw0 eom T stk PG G tn fn s cut u ts
Proof
  strip_tac >> drule_all frame_reachable_raw_certificate >> strip_tac >>
  `o1_fn_row 3 fn` by metis_tac[EVERY_MEM] >>
  `wf_function fn` by metis_tac[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `all_reachable fn /\ pre_fmp_ops fn` by
    gvs[o1_fn_row_def, make_ssa_input_ok_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        s.vs_inst_idx < LENGTH bb.bb_instructions /\
        inst = EL s.vs_inst_idx bb.bb_instructions` by
    (gvs[active_inst_def] >> metis_tac[MEM_lookup_block]) >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_stage_rel_def]) >>
  qpat_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [fmp_frame_rel_def]) >>
  simp[] >> strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)`
  >- suspend "planned" >> suspend "idle"
QED

Resume focus_fmp_cut_restore_prefix[idle]:
  `fmp_frame_rel sm fmp0 raw0 (fmp_frame_base raw0 stk)
     (fmp_frame_lo fmp0 ts) lo T fn fn' PG G tn.t_var s t` by
    (irule fmp_restore_idle_frame >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     qexistsl [`ctx`, `infos`, `runner`] >> gvs[]) >>
  drule_all fmp_restore_active_bound >> strip_tac >>
  `t.vs_inst_idx < LENGTH bb'.bb_instructions` by metis_tac[] >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb'` by metis_tac[] >>
  `!fuel. fmp_target_run fuel C' fn.fn_name t 0 t` by
    (irule fmp_restore_target_run_zero >> qexistsl [`bb'`, `fn'`] >> gvs[]) >>
  `FLOOKUP (fmp_stage_plan infos ctx fn) (s.vs_current_bb,s.vs_inst_idx) = NONE` by
    simp[FLOOKUP_DEF] >>
  `DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < lo} = sm` by
    metis_tac[fmp_restrict_identity] >>
  qexistsl [`bb'`, `infos`, `ctx`, `runner`, `0`, `t`, `lo`] >>
  gvs[fmp_stage_rel_def]
QED

Resume focus_fmp_cut_restore_prefix[planned]:
  drule_all fmp_restore_planned_position >> strip_tac >>
  gvs[] >>
  `~(t.vs_current_bb = rl /\ s.vs_inst_idx < rp)` by metis_tac[] >>
  gvs[] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = t.vs_current_bb` by
    (fs[lookup_block_def] >>
     drule venomInstTheory.FIND_MEM >> drule venomInstTheory.FIND_P >> simp[]) >>
  `?target. FLOOKUP (fmp_stage_plan infos ctx fn)
    (bb.bb_label,s.vs_inst_idx) = SOME target` by gvs[FLOOKUP_DEF] >>
  `df_at NONE states bb.bb_label s.vs_inst_idx = SOME st` by metis_tac[] >>
  drule_all fmp_restore_planned_target >> strip_tac >>
  Cases_on `fmp_pop_at infos fn (liveness_analyze fn) env
    (bb.bb_label,s.vs_inst_idx) (EL s.vs_inst_idx bb.bb_instructions) st` >>
  fs[] >> drule_all fmp_restore_partition >> simp[] >> strip_tac >>
  qabbrev_tac `ps = TAKE (LENGTH q) regions` >>
  qabbrev_tac `ks = DROP (LENGTH q) regions` >>
  `regions = ps ++ ks` by simp[Abbr `ps`, Abbr `ks`] >>
  `ps <> []` by (strip_tac >> gvs[]) >>
  gvs[] >>
  `EVERY (\r. fmp_frame_lo (w2n t.vs_initial_fmp) ts <= r.fr_lo) (ps ++ ks)` by simp[] >>
  drule_all fmp_stage_cut_bounds >> strip_tac >>
  `lookup_var (LAST ps).fr_mark t = SOME (n2w (LAST ps).fr_lo)` by
    (drule fmpLedgerPropsTheory.fmp_ledger_mark >>
     disch_then (qspec_then `LAST ps` mp_tac) >> simp[LAST_MEM]) >>
  suspend "execute"
QED

Resume focus_fmp_cut_restore_prefix[execute]:
  drule_all fmp_restore_planned_needs >> strip_tac >>
  `!rl' rp'. fmp_stage_root infos ctx fn = SOME (rl',rp') /\
     bb.bb_label = rl' ==> rp' <= s.vs_inst_idx` by (rpt strip_tac >> gvs[]) >>
  `?bb' id. lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions s.vs_inst_idx < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions s.vs_inst_idx) bb'.bb_instructions =
      mk_inst id ASSIGN [Var (LAST ps).fr_mark] [runner]` by
    (irule fmp_restore_lowered_code >> simp[] >> qexists `info` >> simp[]) >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
   t.vs_inst_idx < LENGTH bb'.bb_instructions /\
   EL t.vs_inst_idx bb'.bb_instructions =
      mk_inst id ASSIGN [Var (LAST ps).fr_mark] [runner]` by gvs[] >>
  drule_all fmp_restore_target_run >> strip_tac >>
  qabbrev_tac `cut = (LAST ps).fr_lo` >>
  qabbrev_tac `sm' = DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut}` >>
  qabbrev_tac `t1 = (update_var runner (n2w cut) t) with vs_inst_idx := SUC t.vs_inst_idx` >>
  suspend "transport"
QED

Resume focus_fmp_cut_restore_prefix[transport]:
  `!b z c id. FLOOKUP sm (b,z) = SOME (c,id) /\
    b < fmp_frame_base (w2n vs.vs_fmp) stk ==>
    c + z <= fmp_frame_lo (w2n t.vs_initial_fmp) ts` by metis_tac[] >>
  `sm' = DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < (LAST ps).fr_lo}` by
    simp[Abbr `sm'`, Abbr `cut`] >>
  `fmp_env_rel sm' fn
    (live_vars_at (liveness_analyze fn) t.vs_current_bb s.vs_inst_idx) G tn.t_var s t` by
    (drule (PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND]
       (Q.INST [`p` |-> `(t.vs_current_bb,s.vs_inst_idx)`] (SPEC_ALL fmp_restore_cut_env))) >>
     disch_then irule >> simp[Abbr `sm'`, Abbr `cut`] >>
     (conj_tac >- metis_tac[]) >>
     qexistsl [`fmp_frame_base (w2n vs.vs_fmp) stk`,
       `fmp_frame_lo (w2n t.vs_initial_fmp) ts`, `w2n t.vs_initial_fmp`,
       `s.vs_fmp`, `w2n vs.vs_fmp`, `sm`] >> simp[] >> metis_tac[]) >>
  suspend "update"
QED

Resume focus_fmp_cut_restore_prefix[update]:
  `!j. MEM j (fn_insts fn) ==> ~MEM runner j.inst_outputs` by
    (drule_all focus_fmp_selected_root_pin >> strip_tac >>
     `fn'' = fn'` by gvs[] >>
     qpat_assum `!infos ctx runner rl rp. _` (qspecl_then [`infos`, `ctx`, `runner`, `rl`, `rp`] mp_tac) >>
     simp[]) >>
  `~MEM runner (MAP (\r. r.fr_mark) (ps ++ ks))` by
    (drule_all fmp_reclaim_states_stack >>
     simp[EVERY_MEM, fmp_dalloca_output_def] >> metis_tac[]) >>
  drule_all fmpLedgerPropsTheory.fmp_ledger_split >> strip_tac >>
  `fmp_ledger_ok (fn_insts fn) env t1 cut ks` by
    (`fmp_ledger_ok (fn_insts fn) env (update_var runner (n2w cut) t) cut ks` by
       (irule fmpLedgerPropsTheory.fmp_ledger_update_fresh >>
        simp[Abbr `cut`] >> metis_tac[MEM_APPEND, MAP_APPEND]) >>
     simp[Abbr `t1`] >> irule fmpLedgerPropsTheory.fmp_ledger_frame >>
     goal_assum (drule_at Any) >> simp[lookup_var_def]) >>
  `fmp_env_rel sm' fn
    (live_vars_at (liveness_analyze fn) t.vs_current_bb s.vs_inst_idx) G tn.t_var s t1` by
    (`~MEM runner (live_vars_at (liveness_analyze fn) t.vs_current_bb s.vs_inst_idx)` by
       metis_tac[fmpStageFmpStepsLiveTheory.fmp_stage_runner_not_live] >>
     qpat_assum `fmp_env_rel sm' _ _ _ _ s t` mp_tac >>
     simp[NoAsms, Abbr `t1`, fmp_env_rel_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  suspend "cut_fields"
QED

Resume focus_fmp_cut_restore_prefix[cut_fields]:
  `fmp_sites_ok sm' (w2n t.vs_initial_fmp) (w2n vs.vs_fmp) cut s.vs_fmp` by
    (drule_all fmp_restore_cut_sites >> simp[Abbr `cut`]) >>
  `fmp_frame_covers sm' env (fmp_frame_base (w2n vs.vs_fmp) stk) cut G` by
    (irule fmp_restore_cut_covers >>
     qexistsl [`lo`, `sm`] >> simp[Abbr `sm'`]) >>
  `fmp_ledger_link sm' (fmp_frame_base (w2n vs.vs_fmp) stk) cut ks` by
    (drule_all fmp_restore_cut_link >> simp[Abbr `cut`]) >>
  `!b z. 0 < z /\ b + z <= fmp_frame_base (w2n vs.vs_fmp) stk ==>
    FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)` by
    (simp[NoAsms, Abbr `sm'`] >> rpt strip_tac >> irule fmp_caller_lookup_restrict >>
     simp[] >>
     qexistsl [`fmp_frame_base (w2n vs.vs_fmp) stk`, `fmp_frame_lo (w2n t.vs_initial_fmp) ts`] >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `fmp_params_rel sm' PG s t1` by
    (`EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==>
              b + z <= fmp_frame_base (w2n vs.vs_fmp) stk) PG` by
       (irule (cj 5 focus_fmp_frame_sites_upto) >>
        rpt (goal_assum (drule_at Any)) >> simp[]) >>
     `fmp_params_rel sm' PG s t` by
       (qpat_assum `fmp_params_rel sm PG s t`
          (mp_then Any mp_tac fmp_params_rel_transport) >>
        disch_then irule >> rpt strip_tac >>
        first_x_assum irule >>
        qpat_assum `EVERY _ PG` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
        disch_then (qspec_then `k` mp_tac) >> simp[]) >>
     qpat_assum `fmp_params_rel sm' PG s t` mp_tac >>
     simp[NoAsms, Abbr `t1`, fmp_params_rel_def, update_var_def]) >>
  suspend "saved"
QED

Resume focus_fmp_cut_restore_prefix[saved]:
  `!f. MEM f stk ==>
    (!v b z. FLOOKUP f.cf_prov v = SOME (b,z) /\ 0 < z ==>
       b + z <= fmp_frame_base (w2n vs.vs_fmp) stk) /\
    (!k b z. k < LENGTH f.cf_params /\ EL k f.cf_params = SOME (b,z) /\ 0 < z ==>
       b + z <= fmp_frame_base (w2n vs.vs_fmp) stk)` by
    (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`) cut_restore_saved_bounds >>
     disch_then (qspec_then `n` mp_tac) >> pure_asm_rewrite_tac[] >> simp[NoAsms]) >>
  `fmp_saved_rel C' sm' (w2n t.vs_initial_fmp) (w2n vs.vs_fmp) stk ts` by
    (simp[NoAsms, Abbr `sm'`] >> irule fmp_saved_rel_drestrict >>
     reverse conj_tac >- (metis_tac[]) >>
     metis_tac[]) >>
  `w2n t.vs_initial_fmp <= cut` by
    (`w2n t.vs_initial_fmp <= fmp_frame_lo (w2n t.vs_initial_fmp) ts` by
       (Cases_on `stk` >> namedCases_on `ts` ["", "hd tl"] >>
        fs[fmp_saved_rel_def, fmp_frame_lo_def] >>
        PairCases_on `hd` >> fs[fmp_saved_rel_def, fmp_frame_lo_def] >>
        gvs[fmp_frame_rel_def, fmpLowerSequenceExecTheory.fmp_frontier_rel_def]) >>
     decide_tac) >>
  suspend "reconstruct"
QED

Resume focus_fmp_cut_restore_prefix[reconstruct]:
  `!b z c id. FLOOKUP sm' (b,z) = SOME (c,id) ==>
    (fmp_frame_base (w2n vs.vs_fmp) stk <= b <=>
     fmp_frame_lo (w2n t.vs_initial_fmp) ts <= c) /\
    (b < fmp_frame_base (w2n vs.vs_fmp) stk ==>
     c + z <= fmp_frame_lo (w2n t.vs_initial_fmp) ts /\
     b + z <= fmp_frame_base (w2n vs.vs_fmp) stk)` by
    (simp[NoAsms, Abbr `sm'`, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
     qpat_assum `!b z c id. FLOOKUP sm (b,z) = _ ==> _` drule >> simp[]) >>
  `fmp_frame_rel sm' (w2n t.vs_initial_fmp) (w2n vs.vs_fmp)
     (fmp_frame_base (w2n vs.vs_fmp) stk)
     (fmp_frame_lo (w2n t.vs_initial_fmp) ts) cut T fn fn' PG G tn.t_var s t1` by
    (qpat_x_assum `Abbrev (ps = _)` kall_tac >>
     qpat_x_assum `Abbrev (ks = _)` kall_tac >>
     irule fmp_restore_postroot_frame >>
     rpt conj_tac
     >- first_assum MATCH_ACCEPT_TAC
     >- first_assum MATCH_ACCEPT_TAC
     >- first_assum MATCH_ACCEPT_TAC
     >- first_assum MATCH_ACCEPT_TAC
     >- simp[]
     >- (qexists `lo` >> conj_tac >> first_assum MATCH_ACCEPT_TAC)
     >- simp[]
     >- (qexistsl [`ctx`, `env`, `infos`, `bb.bb_instructions`, `ks`,
                   `fmp_stage_plan infos ctx fn`, `rl`, `rp`, `runner`, `st`, `states`, `t`] >>
         qpat_assum `s.vs_current_bb = _` (fn th => rewrite_tac[th]) >>
         rpt conj_tac >> simp[Abbr `t1`]) >>
     metis_tac[]) >>
  suspend "joint"
QED

Resume focus_fmp_cut_restore_prefix[joint]:
  `ld_memory_agree (fmp_ld_sites sm') eom tn.t_mem s.vs_memory t.vs_memory` by
    (simp[NoAsms, Abbr `sm'`] >> irule fmp_memory_agree_drestrict >>
     first_assum MATCH_ACCEPT_TAC) >>
  `fmp_stage_rel D C' sm' (w2n t.vs_initial_fmp) (w2n vs.vs_fmp)
     eom T stk PG G tn fn s cut t1 ts` by
    (simp[NoAsms, fmp_stage_rel_def] >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >- (qexists `fn'` >> conj_tac >> first_assum MATCH_ACCEPT_TAC)) >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     simp[NoAsms, Abbr `t1`, update_var_def] >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >-
       (qpat_assum `ld_shared_agree _ _ _ _ _` mp_tac >>
        simp[NoAsms, o1LowerDloadSharedTheory.ld_shared_agree_def] >> simp[])) >>
     simp[]) >>
  qexistsl [`bb'`, `infos`, `ctx`, `runner`, `1`, `t1`, `cut`] >>
  qpat_x_assum `Abbrev (ps = _)` kall_tac >>
  qpat_x_assum `Abbrev (ks = _)` kall_tac >>
  `t1.vs_current_bb = t.vs_current_bb /\ t1.vs_inst_idx = 1 + t.vs_inst_idx` by
    simp[NoAsms, Abbr `t1`, update_var_def, arithmeticTheory.ADD1] >>
  `1 + t.vs_inst_idx <= LENGTH bb'.bb_instructions` by decide_tac >>
  qpat_x_assum `t.vs_inst_idx = fmp_stage_tidx _ _ _ _ _` SUBST_ALL_TAC >>
  pure_asm_rewrite_tac[] >> simp[NoAsms] >>
  conj_tac
  >- (qexistsl [`id`, `n2w cut`] >> pure_asm_rewrite_tac[] >>
      simp[NoAsms, Abbr `t1`]) >>
  qpat_assum `Abbrev (sm' = _)`
    (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  first_assum ACCEPT_TAC
QED

Finalise focus_fmp_cut_restore_prefix
