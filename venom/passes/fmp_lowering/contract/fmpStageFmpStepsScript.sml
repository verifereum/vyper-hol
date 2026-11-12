(*
 * FmpLowering's stage simulation, the FMP-specific steps: a point's
 * reclaim restore, DALLOCA's 4-instruction expansion, RETPC_PARAM with the
 * root, the context entry's frame, and INVOKE's call and return.  Each
 * keeps fmpStageRel's joint relation, with the site map sm and the runner
 * lo moved as the step frees or makes sites.
 *
 * TOP-LEVEL:
 *   fmp_stage_restore        - the restores at a source point (F -> T)
 *   fmp_stage_dalloca_step   - DALLOCA against its expansion
 *   fmp_stage_retpc_step     - RETPC_PARAM, with the root before it
 *   fmp_stage_entry          - the context entry's first related point
 *   fmp_stage_invoke_call    - INVOKE, into the callee's first point
 *   fmp_stage_invoke_return  - RET, back to the caller past its INVOKE
 *)
Theory fmpStageFmpSteps
Ancestors
  fmpStageOpBase fmpStageControl fmpStageReclaimSound fmpStageRel
  fmpStageCallArity fmpStageRetStep
  fmpStageFmpStepsRestoreControl fmpStageFmpStepsRestoreCut
  fmpStageFmpStepsRestoreIdle fmpStageFmpStepsRestoreFrame
  fmpStageFmpStepsLedgerSaved fmpRestoreProps
  fmpStageFmpStepsRestoreBounds fmpStageFmpStepsRestorePosition
  fmpStageFmpStepsEntryLayout fmpStageFmpStepsEntryInitialization
  ptrStaticDiscipline o1PassContract
  ptrDiscipline venomExecSemantics venomState venomInst finite_map words
  list rich_list fmpStageFmpStepsLedgerPartition

Theorem fmp_restore_env_update_dead[local]:
  fmp_env_rel sm fn live G tv s t /\ ~MEM runner live ==>
  fmp_env_rel sm fn live G tv s
    ((update_var runner value t) with vs_inst_idx := idx)
Proof
  rw[fmp_env_rel_def, update_var_def] >>
  Cases_on `v = runner` >- (gvs[] >> qexists `value` >> simp[FLOOKUP_UPDATE]) >>
  first_x_assum drule >> strip_tac >> qexists `y` >> simp[FLOOKUP_UPDATE]
QED

Theorem fmp_restore_saved_lower[local]:
  !stk ts. fmp_saved_rel C' sm fmp0 raw0 stk ts ==>
  fmp0 <= fmp_frame_lo fmp0 ts
Proof
  Induct >> Cases_on `ts` >> simp[fmp_saved_rel_def, fmp_frame_lo_def] >>
  PairCases_on `h` >> simp[fmp_saved_rel_def, fmp_frame_lo_def] >>
  rpt strip_tac >> first_x_assum drule >>
  gvs[fmp_frame_rel_def] >> decide_tac
QED

Theorem fmp_restore_live_ir[local]:
  MEM v (live_vars_at (liveness_analyze fn) lbl idx) ==>
  MEM v (fn_ir_vars fn)
Proof
  strip_tac >>
  qspecl_then [`fn`, `lbl`, `idx`, `v`] mp_tac livenessProofsTheory.live_vars_bounded >>
  simp[livenessDefsTheory.fn_all_vars_def, irSupplyTheory.fn_ir_vars_def,
    irSupplyTheory.block_ir_vars_def, irSupplyTheory.inst_ir_vars_def,
    inst_defs_def, MEM_FLAT, MEM_MAP] >>
  strip_tac >> gvs[MEM_FLAT, MEM_MAP, irSupplyTheory.inst_ir_vars_def,
                   MEM_APPEND] >>
  (qexists `FLAT (MAP inst_ir_vars bb.bb_instructions)` >>
   (conj_tac >- metis_tac[]) >>
   simp[MEM_FLAT, MEM_MAP] >> qexists `inst_ir_vars inst` >>
   simp[irSupplyTheory.inst_ir_vars_def] >> metis_tac[])
QED

Theorem fmp_restore_runner_dead[local]:
  fmp_stage_lowered infos ctx runner fn fn' ==>
  ~MEM runner (live_vars_at (liveness_analyze fn) lbl idx)
Proof
  rw[fmp_stage_lowered_def] >>
  Cases_on `fresh_ir_var sp` >> gvs[] >>
  drule (cj 1 irSupplyTheory.fresh_ir_var_contract) >> strip_tac >>
  gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
      venomFnScheduleRunnerTheory.list_subset_def] >>
  strip_tac >> drule fmp_restore_live_ir >> strip_tac >> fs[EVERY_MEM] >>
  qpat_x_assum `!x. MEM x (fn_ir_vars fn) ==> _` drule >> simp[]
QED

Theorem fmp_stage_restore:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts ==>
  ?n t1 lo'.
    (!k. fmp_target_run k C' fn.fn_name t n t1) /\ lo' <= lo /\
    n <= 1 /\
    (n = 1 ==>
     ?fn' bb'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
       (EL t.vs_inst_idx bb'.bb_instructions).inst_opcode = ASSIGN) /\
    fmp_stage_rel D C'
      (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < lo'})
      fmp0 raw0 eom T stk PG G tn fn s lo' t1 ts
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[o1_fn_shape_def, venomWfTheory.wf_function_def,
        venomInstTheory.fn_labels_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        s.vs_inst_idx < LENGTH bb.bb_instructions /\
        inst = EL s.vs_inst_idx bb.bb_instructions` by
    (gvs[contextCodegenRelTheory.active_inst_def] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_stage_rel_def]) >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >> simp[fmp_frame_rel_def] >> strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) IN
    FDOM (fmp_stage_plan infos ctx fn)`
  >- suspend "planned" >>
  suspend "idle"
QED

Resume fmp_stage_restore[planned]:
  drule_all fmp_restore_planned_position >> strip_tac >>
  gvs[] >>
  `~(t.vs_current_bb = rl /\ s.vs_inst_idx < rp)` by metis_tac[] >>
  gvs[] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = t.vs_current_bb` by
    (fs[lookup_block_def] >>
     drule venomInstTheory.FIND_MEM >> drule venomInstTheory.FIND_P >> simp[]) >>
  `?target. FLOOKUP (fmp_stage_plan infos ctx fn)
    (bb.bb_label,s.vs_inst_idx) = SOME target` by
    gvs[FLOOKUP_DEF] >>
  `df_at NONE states bb.bb_label s.vs_inst_idx = SOME st` by metis_tac[] >>
  drule_all fmp_restore_planned_target >> strip_tac >>
  Cases_on `fmp_pop_at infos fn (liveness_analyze fn) env
    (bb.bb_label,s.vs_inst_idx) (EL s.vs_inst_idx bb.bb_instructions) st` >>
  fs[] >> drule_all fmp_restore_partition >> simp[] >> strip_tac >>
  qabbrev_tac `ps = TAKE (LENGTH q) regions` >>
  qabbrev_tac `ks = DROP (LENGTH q) regions` >>
  `regions = ps ++ ks` by simp[Abbr `ps`, Abbr `ks`] >>
  `ps <> []` by (strip_tac >> gvs[]) >>
  gvs[] >> drule fmp_stage_cut_bounds >>
  disch_then (qspec_then `fmp_frame_lo (w2n vs'.vs_initial_fmp) ts` mp_tac) >>
  simp[] >> strip_tac >>
  `lookup_var (LAST ps).fr_mark t = SOME (n2w (LAST ps).fr_lo)` by
    (drule fmpLedgerPropsTheory.fmp_ledger_mark >>
     disch_then (qspec_then `LAST ps` mp_tac) >> simp[LAST_MEM]) >>
  suspend "execute"
QED

Resume fmp_stage_restore[idle]:
  `fmp_frame_rel sm (w2n vs'.vs_initial_fmp) (w2n fmp)
     (fmp_frame_base (w2n fmp) stk)
     (fmp_frame_lo (w2n vs'.vs_initial_fmp) ts) lo T
     fn fn' PG G tn.t_var s t` by
    (irule fmp_restore_idle_frame >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     qexistsl [`ctx`, `infos`, `runner`] >> gvs[]) >>
  `DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < lo} = sm` by
    metis_tac[fmpStageFmpStepsLedgerRestrictTheory.fmp_restrict_identity] >>
  qexistsl [`0`, `t`, `lo`] >> simp[fmp_stage_rel_def] >>
  reverse conj_tac >- metis_tac[] >>
  drule_all fmp_restore_active_bound >> strip_tac >>
  irule fmp_restore_target_run_zero >>
  qexistsl [`bb'`, `fn'`] >> gvs[]
QED

Resume fmp_stage_restore[execute]:
  drule_all fmp_restore_planned_needs >> strip_tac >>
  `!rl' rp'. fmp_stage_root infos ctx fn = SOME (rl',rp') /\
     bb.bb_label = rl' ==> rp' <= s.vs_inst_idx` by (rpt strip_tac >> gvs[] >> decide_tac) >>
  `?bb' id. lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions s.vs_inst_idx < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions s.vs_inst_idx) bb'.bb_instructions =
      mk_inst id ASSIGN [Var (LAST ps).fr_mark] [runner]` by
    (irule fmp_restore_lowered_code >> simp[] >>
     qexists `info` >> simp[]) >>
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

Resume fmp_stage_restore[transport]:
  `!b z c id. FLOOKUP sm (b,z) = SOME (c,id) /\
    b < fmp_frame_base (w2n s.vs_initial_fmp) stk ==>
    c + z <= fmp_frame_lo (w2n vs'.vs_initial_fmp) ts` by metis_tac[] >>
  `fmp_env_rel sm' fn
    (live_vars_at (liveness_analyze fn) t.vs_current_bb s.vs_inst_idx) G tn.t_var s t` by
    (`EVERY (\r. fmp_frame_lo (w2n vs'.vs_initial_fmp) ts <= r.fr_lo) (ps ++ ks)` by simp[] >>
     `sm' = DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < (LAST ps).fr_lo}` by
       simp[Abbr `sm'`, Abbr `cut`] >>
     drule (PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND]
       (Q.INST [`p` |-> `(t.vs_current_bb,s.vs_inst_idx)`] (SPEC_ALL fmp_restore_cut_env))) >>
     disch_then irule >> simp[Abbr `sm'`, Abbr `cut`] >>
     (conj_tac >- metis_tac[]) >>
     qexistsl [`fmp_frame_base (w2n s.vs_initial_fmp) stk`,
       `fmp_frame_lo (w2n vs'.vs_initial_fmp) ts`, `w2n vs'.vs_initial_fmp`,
       `s.vs_fmp`, `w2n s.vs_initial_fmp`, `sm`] >> simp[] >> metis_tac[]) >>
  suspend "frame"
QED

Resume fmp_stage_restore[frame]:
  `~MEM runner (MAP (\r. r.fr_mark) (ps ++ ks))` by
    (drule_all fmp_stage_witness_pin >> strip_tac >>
     drule_all fmpStepAnalysisTheory.fmp_reclaim_states_stack >>
     gvs[EVERY_MEM, fmpStepStackTheory.fmp_dalloca_output_def] >> metis_tac[]) >>
  drule_all fmpLedgerPropsTheory.fmp_ledger_split >> strip_tac >>
  `fmp_ledger_ok (fn_insts fn) env (update_var runner (n2w cut) t) cut ks` by
    (irule fmpLedgerPropsTheory.fmp_ledger_update_fresh >>
     gvs[Abbr `cut`, MEM_MAP, MEM_APPEND]) >>
  `fmp_ledger_ok (fn_insts fn) env t1 cut ks` by
    (simp[Abbr `t1`] >> irule fmpLedgerPropsTheory.fmp_ledger_frame >>
     goal_assum (drule_at Any) >> simp[lookup_var_def]) >>
  `fmp_env_rel sm' fn
    (live_vars_at (liveness_analyze fn) t.vs_current_bb s.vs_inst_idx) G tn.t_var s t1` by
    (simp[Abbr `t1`] >> irule fmp_restore_env_update_dead >>
     simp[] >> metis_tac[fmp_restore_runner_dead]) >>
  suspend "cutfields"
QED

Resume fmp_stage_restore[cutfields]:
  `EVERY (\r. fmp_frame_lo (w2n vs'.vs_initial_fmp) ts <= r.fr_lo) (ps ++ ks)` by simp[] >>
  `sm' = DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < (LAST ps).fr_lo}` by
    simp[Abbr `sm'`, Abbr `cut`] >>
  `fmp_sites_ok sm' (w2n vs'.vs_initial_fmp) (w2n s.vs_initial_fmp) cut s.vs_fmp` by
    (drule_all fmp_restore_cut_sites >> simp[Abbr `cut`]) >>
  `fmp_frame_covers sm' env (fmp_frame_base (w2n s.vs_initial_fmp) stk) cut G` by
    (irule fmp_restore_cut_covers >> metis_tac[]) >>
  `fmp_ledger_link sm' (fmp_frame_base (w2n s.vs_initial_fmp) stk) cut ks` by
    (drule_all fmp_restore_cut_link >> simp[Abbr `cut`]) >>
  `fmp_params_rel sm' PG s t` by
    (simp[NoAsms, Abbr `sm'`] >> irule fmp_restore_params_rel >> metis_tac[]) >>
  `fmp_params_rel sm' PG s t1` by
    (simp[NoAsms, Abbr `t1`, fmp_params_rel_def, update_var_def] >>
     qpat_x_assum `fmp_params_rel sm' PG s t` mp_tac >>
     metis_tac[fmp_params_rel_def]) >>
  `w2n vs'.vs_initial_fmp <= cut` by
    (drule fmp_restore_saved_lower >> strip_tac >> decide_tac) >>
  suspend "reconstruct"
QED

Resume fmp_stage_restore[reconstruct]:
  `!b z c id. FLOOKUP sm' (b,z) = SOME (c,id) ==>
    (fmp_frame_base (w2n s.vs_initial_fmp) stk <= b <=>
     fmp_frame_lo (w2n vs'.vs_initial_fmp) ts <= c) /\
    (b < fmp_frame_base (w2n s.vs_initial_fmp) stk ==>
     c + z <= fmp_frame_lo (w2n vs'.vs_initial_fmp) ts /\
     b + z <= fmp_frame_base (w2n s.vs_initial_fmp) stk)` by
    (simp[NoAsms, Abbr `sm'`, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
     qpat_x_assum `!b z c id. FLOOKUP sm (b,z) = _ ==> _` drule >> simp[]) >>
  `fmp_frame_rel sm' (w2n vs'.vs_initial_fmp) (w2n s.vs_initial_fmp)
    (fmp_frame_base (w2n s.vs_initial_fmp) stk)
    (fmp_frame_lo (w2n vs'.vs_initial_fmp) ts) cut T fn fn' PG G tn.t_var s t1` by
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

Resume fmp_stage_restore[joint]:
  `fmp_saved_rel C' sm' (w2n vs'.vs_initial_fmp) (w2n s.vs_initial_fmp) stk ts` by
    (simp[NoAsms, Abbr `sm'`] >> irule fmp_restore_saved_rel >> metis_tac[]) >>
  `ld_memory_agree (fmp_ld_sites sm') eom tn.t_mem s.vs_memory t.vs_memory` by
    (simp[NoAsms, Abbr `sm'`] >>
     irule fmpStageFmpStepsLedgerRestrictTheory.fmp_memory_agree_restrict >>
     first_assum MATCH_ACCEPT_TAC) >>
  qexistsl [`1`, `t1`, `cut`] >>
  qpat_x_assum `Abbrev (ps = _)` kall_tac >>
  qpat_x_assum `Abbrev (ks = _)` kall_tac >>
  simp[NoAsms] >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  (conj_tac >- metis_tac[]) >>
  `fmp_stage_rel D C' sm' (w2n vs'.vs_initial_fmp)
    (w2n s.vs_initial_fmp) eom T stk PG G tn fn s cut t1 ts`
    suffices_by simp[NoAsms, Abbr `sm'`] >>
  simp[NoAsms, fmp_stage_rel_def] >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  (conj_tac >- (qexists `fn'` >> conj_tac >> first_assum MATCH_ACCEPT_TAC)) >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  simp[NoAsms, Abbr `t1`, update_var_def] >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  (conj_tac >-
    (qpat_x_assum `ld_shared_agree _ _ _ _ _` mp_tac >>
     simp[NoAsms, o1LowerDloadSharedTheory.ld_shared_agree_def] >>
     simp[])) >>
  simp[]
QED

Finalise fmp_stage_restore

Theorem fmp_stage_dalloca_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = DALLOCA /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1 t1.
    r = OK s1 /\ (!k'. fmp_target_run k' C' fn.fn_name t 4 t1) /\
    fmp_stage_rel D C'
      (if w2n s1.vs_fmp = w2n s.vs_fmp then sm
       else sm |+ ((w2n s.vs_fmp, w2n s1.vs_fmp - w2n s.vs_fmp),
                  (lo, inst.inst_id)))
      fmp0 raw0 eom F stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (lo + (w2n s1.vs_fmp - w2n s.vs_fmp)) t1 ts
Proof
  cheat
QED

Theorem fmp_stage_retpc_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = RETPC_PARAM /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1 n t1.
    r = OK s1 /\ 1 <= n /\ n <= 2 /\
    (!k'. fmp_target_run k' C' fn.fn_name t n t1) /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
      (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo t1 ts
Proof
  cheat
QED

Theorem fmp_stage_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                vs_inst_idx := 0 |>) s1 /\
  active_inst fn inst s1 ==>
  ?n t1.
    (!k. fmp_target_run k C' name
           (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                        vs_inst_idx := 0 |>) n t1) /\
    fmp_stage_rel D C' FEMPTY (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      [] [] FEMPTY entry_taint fn s1 (w2n vs'.vs_initial_fmp) t1 []
Proof
  strip_tac >>
  drule_all fmp_entry_source_shape >> strip_tac >> gvs[] >>
  `wf_function fn` by
    (gvs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def, lookup_function_MEM]) >>
  `fn.fn_fmp_signature = NONE` by
    (gvs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def,
         fmp_free_ctx_def, EVERY_MEM] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all fmp_entry_actual_lowering >> strip_tac >>
  `fn_is_context_entry ctx fn` by simp[fmpWfDefsTheory.fn_is_context_entry_def] >>
  drule_all fmp_entry_root_position >> strip_tac >>
  drule_all fmp_entry_target_block >> strip_tac >>
  irule fmp_stage_entry_from_layout >>
  simp[] >>
  (reverse conj_tac >- metis_tac[]) >>
  qexistsl_tac [`ctx`, `infos`, `runner`] >>
  simp[] >> strip_tac >>
  drule_all fmp_entry_initial_prefix >> strip_tac >> gvs[] >>
  qexists_tac `id` >> simp[]
QED

Theorem fmp_stage_invoke_call:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ~s.vs_halted /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\ C.ctx_entry <> SOME nm /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ivk' t ==>
  ?ops' callee' args' cs' t1.
    ivk'.inst_opcode = INVOKE /\ decode_invoke ivk' = SOME (nm,ops') /\
    lookup_function nm C'.ctx_functions = SOME callee' /\
    eval_operands ops' t = SOME args' /\
    setup_callee callee' args' t = SOME cs' /\
    enters_block callee' cs' t1 /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F
      (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
          cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
      lo t1 ((t,lo)::ts)
Proof
  cheat
QED

Theorem fmp_stage_invoke_return:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C (f::stk) PG G tn fn rinst s /\
  active_inst fn rinst s /\ ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T (f::stk) PG G tn fn s lo t
    ((tc,lc)::ts) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' rinst' t /\
  step_inst k C rinst s = IntRet ret s_end /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
    SOME s' /\
  active_inst f.cf_fn inst'
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ?ret' t_end fc' ivk' t'.
    (!k'. step_inst k' C' rinst' t = IntRet ret' t_end) /\
    ret'.iret_values = ret.iret_values /\
    lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fc' /\
    active_inst fc' ivk' tc /\
    bind_outputs ivk'.inst_outputs ret'.iret_values
      (adopt_return_fmp ret' (merge_callee_state tc t_end)) = SOME t' /\
    fmp_stage_rel D C'
      (DRESTRICT sm {key | FST key < w2n f.cf_state.vs_fmp})
      fmp0 raw0 eom F stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var :=
         DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) lc
      (t' with vs_inst_idx := SUC tc.vs_inst_idx) ts
Proof
  cheat
QED
