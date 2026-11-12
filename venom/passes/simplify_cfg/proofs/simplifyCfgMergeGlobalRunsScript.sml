(* Bidirectional terminating whole-run transport for chain contraction. *)
Theory simplifyCfgMergeGlobalRuns
Ancestors
  simplifyCfgMergeSemantics simplifyCfgMergeRuns simplifyCfgMergeSegment
  simplifyCfgMergePaths simplifyCfgMergeExec simplifyCfgMergeClosure
  simplifyCfgFragments simplifyCfgControl simplifyCfgControlExec
  simplifyCfgSimTools simplifyCfgStaticInterface simplifyCfgDefs
  venomExecSemantics venomExecProps venomExecProofs venomState venomInst
  contextCodegenRel o1PassLift passSimulationDefs venomWf cfgTransform list

Theorem scfg_run_block_terminal:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block k C bb s = r /\ terminates r /\ (!u. r <> OK u) ==>
  ?n. run_blocks n C fn s = r
Proof
  strip_tac >> qexists_tac `SUC k` >>
  Cases_on `r` >> gvs[run_blocks_unfold, terminates_def]
QED

Theorem scfg_chain_terminal_backward:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  run_block n C bt t = q /\ terminates q /\ (!v. q <> OK v) ==>
  ?k. frame_result_rel (run_blocks k C fn s) q
Proof
  strip_tac >> drule_all scfg_chain_exit_lookup >> strip_tac >>
  drule_all scfg_chain_block_backward >> strip_tac >>
  `terminates r /\ (!u. r <> OK u)` by
    (Cases_on `r` >> Cases_on `q` >> fs[scfg_result_def, terminates_def]) >>
  `frame_result_rel r q` by metis_tac[scfg_result_terminal] >>
  `?m. run_blocks m C fn s = r` suffices_by metis_tac[]
  >- (irule scfg_run_block_terminal >> goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (irule scfg_run_block_terminal >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `lookup_block x.vs_current_bb fn.fn_blocks = SOME b` by fs[scfg_chain_hyp_def] >>
  `?m. run_blocks m C fn x = r` by
    (irule scfg_run_block_terminal >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `?j. run_blocks j C fn s = r` by
    (irule scfg_bstep_continue >> conj_tac
     >- (Cases_on `r` >> gvs[terminates_def]) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `j` >> simp[]
QED

Theorem scfg_chain_runs_backward:
  !n t r s. scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  run_blocks n C (scfg_chain fn a b) t = r /\ terminates r ==>
  ?k. frame_result_rel (run_blocks k C fn s) r
Proof
  Induct_on `n` >- simp[Once run_blocks_def, terminates_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_blocks_unfold] >>
  Cases_on `lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks` >>
  simp[] >> strip_tac >- gvs[terminates_def] >>
  rename1 `lookup_block _ _ = SOME bt` >>
  Cases_on `run_block n C bt t` >> gvs[]
  >- (Cases_on `v.vs_halted` >> gvs[]
      >- metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
      drule_all scfg_chain_block_prefix_backward >> strip_tac >>
      `scfg_bprefix C fn s0 u` by metis_tac[scfg_bprefix_trans] >>
      `?k. frame_result_rel (run_blocks k C fn u)
          (run_blocks n C (scfg_chain fn a b) v)` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      `!e. run_blocks k C fn u <> Error e` by
        (drule frame_result_rel_terminates >>
         Cases_on `run_blocks k C fn u` >> simp[terminates_def]) >>
      `?m. run_blocks m C fn s = run_blocks k C fn u` by
        (irule scfg_bprefix_continue >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  irule scfg_chain_terminal_backward >> goal_assum (drule_at Any) >>
  simp[terminates_def] >> metis_tac[]
QED

Theorem scfg_enter_run_block:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  enters_block fn s s1 ==>
  (!k. run_block k C bb s = exec_block k C bb s1) /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  simp[run_block_def] >>
  metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted]
QED

Theorem scfg_chain_run_a_next:
  scfg_chain_hyp fn a b /\ run_block n C a s = OK u ==>
  ~u.vs_halted /\ u.vs_current_bb = b.bb_label
Proof
  strip_tac >> simp[] >> conj_tac
  >- metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `wf_function fn /\ fn_inst_wf fn /\ MEM a fn.fn_blocks` by
    metis_tac[scfg_chain_hyp_def, scfg_chain_old_wf, scfg_normalized_static,
      scfg_static_inst_wf, lookup_block_member_label] >>
  `bb_well_formed a /\ EVERY inst_wf a.bb_instructions` by
    metis_tac[wf_function_bb_well_formed, fn_inst_wf_every_bb] >>
  `MEM u.vs_current_bb (bb_succs a)` by
    (irule venomExecPropsTheory.run_block_current_bb_in_succs >>
     conj_tac
     >- (gvs[bb_well_formed_def] >> rpt strip_tac >>
         `i < LENGTH a.bb_instructions` by decide_tac >>
         first_x_assum drule_all >> decide_tac) >>
     gvs[bb_well_formed_def] >> metis_tac[]) >>
  gvs[scfg_chain_hyp_def, can_merge_blocks_def]
QED

(* Same-budget forward transport. *)
Theorem scfg_chain_block_forward_fuel[local]:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ((run_block N C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?x. bb.bb_label = a.bb_label /\
       run_block N C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block N C b x = r)) /\
  terminates r ==>
  ?bt q. lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    run_block N C bt t = q /\ scfg_result r q /\
    (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_current_bb <> b.bb_label` by fs[scfg_chain_exit_def] >>
  `?s1. enters_block fn s s1` by
    (qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
     >- (simp[enters_block_def] >> metis_tac[]) >>
     Cases_on `r` >> gvs[run_block_def, terminates_def]) >>
  drule_all scfg_chain_rooted_incoming >> strip_tac >>
  drule_all scfg_chain_enters_segment >> strip_tac >>
  drule scfg_chain_exit_ctrl >> disch_then SUBST_ALL_TAC >>
  `?bt. lookup_block
      (scfg_ctrl s.vs_current_bb
        (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) 0 s).vs_current_bb
      (scfg_chain fn a b).fn_blocks = SOME bt` by
    (simp[scfg_ctrl_def, scfg_chain_lookup_eq] >> metis_tac[]) >>
  qpat_assum `enters_block fn s s1` (mp_then Any mp_tac scfg_enter_run_block) >>
  disch_then drule >> disch_then (qspec_then `C` strip_assume_tac) >>
  qpat_assum `enters_block (scfg_chain fn a b) _ t1`
    (mp_then Any mp_tac scfg_enter_run_block) >>
  disch_then drule >> disch_then (qspec_then `C` strip_assume_tac) >>
  `(!i. active_inst fn i s1 ==> frame_reach C fn s0 i s1)` by
    metis_tac[scfg_bprefix_enter_reach] >>
  `?q. exec_block N C bt t1 = q /\ scfg_result r q /\
      (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)` by
    (irule scfg_chain_exec_forward_fuel >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`bt`, `q`] >> simp[] >>
  qpat_x_assum `enters_block (scfg_chain fn a b) _ t1` mp_tac >>
  simp[enters_block_def] >> strip_tac >> gvs[] >> fs[run_block_def]
QED

Theorem scfg_chain_terminal_forward_fuel[local]:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ((run_block N C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?x. bb.bb_label = a.bb_label /\
       run_block N C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block N C b x = r)) /\
  terminates r /\ (!v. r <> OK v) ==>
  frame_result_rel r (run_blocks (SUC N) C (scfg_chain fn a b) t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scfg_chain_block_forward_fuel >> strip_tac >>
  `terminates q /\ (!v. q <> OK v)` by
    (Cases_on `r` >> Cases_on `q` >> gvs[scfg_result_def, terminates_def]) >>
  `frame_result_rel r q` by metis_tac[scfg_result_terminal] >>
  `run_blocks (SUC N) C (scfg_chain fn a b) t = q` by
    (Cases_on `q` >> gvs[run_blocks_unfold, terminates_def]) >> simp[]
QED

Theorem scfg_chain_continue_forward_fuel[local]:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ((run_block N C bb s = OK u /\ bb.bb_label <> a.bb_label) \/
   (?x. bb.bb_label = a.bb_label /\
       run_block N C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block N C b x = OK u)) /\
  (!w. scfg_chain_exit a b u w ==>
     frame_result_rel r (run_blocks N C (scfg_chain fn a b) w)) ==>
  frame_result_rel r (run_blocks (SUC N) C (scfg_chain fn a b) t)
Proof
  strip_tac >>
  `?bt q. lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
      run_block N C bt t = q /\ scfg_result (OK u) q /\
      (!u' v. OK u = OK u' /\ q = OK v ==> scfg_chain_exit a b u' v)` by
    (irule scfg_chain_block_forward_fuel >> simp[terminates_def] >> metis_tac[]) >>
  `?w. q = OK w` by (Cases_on `q` >> fs[scfg_result_def]) >>
  qpat_x_assum `q = OK w` SUBST_ALL_TAC >>
  `scfg_chain_exit a b u w` by metis_tac[exec_result_11] >>
  `~w.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  simp[run_blocks_unfold]
QED

Theorem scfg_chain_runs_forward_fuel[local]:
  !n s r t. scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  run_blocks n C fn s = r /\ terminates r ==>
  frame_result_rel r (run_blocks n C (scfg_chain fn a b) t)
Proof
  completeInduct_on `n` >> Cases_on `n`
  >- simp[Once run_blocks_def, terminates_def] >>
  rename1 `SUC m` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [run_blocks_unfold]) >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >> strip_tac
  >- gvs[terminates_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `run_block m C bb s` >> gvs[]
  >- (`~v.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
      gvs[] >> Cases_on `bb.bb_label = a.bb_label`
      >- suspend "pair" >> suspend "single") >>
  irule scfg_chain_terminal_forward_fuel >> goal_assum (drule_at Any) >>
  simp[terminates_def] >> metis_tac[]
QED

Resume scfg_chain_runs_forward_fuel[single]:
  `scfg_bprefix C fn s0 v` by
    metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
  `!w. scfg_chain_exit a b v w ==>
     frame_result_rel (run_blocks m C fn v)
       (run_blocks m C (scfg_chain fn a b) w)` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  irule scfg_chain_continue_forward_fuel >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Resume scfg_chain_runs_forward_fuel[pair]:
  `bb = a` by metis_tac[scfg_chain_old_wf, scfg_chain_hyp_def,
    wf_function_def, venomExecProofsTheory.same_label_same_block,
    lookup_block_member_label] >> gvs[] >>
  drule_all scfg_chain_run_a_next >> strip_tac >>
  `scfg_bprefix C fn s0 v` by
    metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME b` by fs[scfg_chain_hyp_def] >>
  Cases_on `m`
  >- (qpat_x_assum `terminates (run_blocks 0 C fn v)` mp_tac >>
      simp[Once run_blocks_def, terminates_def]) >>
  rename1 `run_block (SUC j) C a s = OK v` >>
  qpat_x_assum `terminates (run_blocks (SUC j) C fn v)`
    (mp_tac o ONCE_REWRITE_RULE [run_blocks_unfold]) >> simp[] >>
  Cases_on `run_block j C b v` >> simp[] >> strip_tac
  >- suspend "pair_continue" >>
  gvs[terminates_def] >>
  `run_block (SUC j) C b v = run_block j C b v` by
    (irule run_block_fuel_mono >> simp[] >> qexists_tac `j` >>
     Cases_on `run_block j C b v` >> gvs[terminates_def]) >>
  `run_blocks (SUC j) C fn v = run_block j C b v` by
    (Cases_on `run_block j C b v` >> gvs[run_blocks_unfold, terminates_def]) >>
  irule scfg_chain_terminal_forward_fuel >> goal_assum (drule_at Any) >>
  simp[terminates_def] >> metis_tac[]
QED

Resume scfg_chain_runs_forward_fuel[pair_continue]:
  rename1 `run_block j C b v = OK u` >>
  `~u.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  gvs[] >>
  `scfg_bprefix C fn s0 u` by
    metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
  `run_block (SUC j) C b v = OK u` by
    (irule run_block_fuel_mono_OK >> qexists_tac `j` >> simp[]) >>
  `!w. scfg_chain_exit a b u w ==>
     frame_result_rel (run_blocks j C fn u)
       (run_blocks (SUC j) C (scfg_chain fn a b) w)` by
    (rpt strip_tac >>
     `frame_result_rel (run_blocks j C fn u)
        (run_blocks j C (scfg_chain fn a b) w)` by
       (first_x_assum irule >> simp[] >> metis_tac[]) >>
     `terminates (run_blocks j C (scfg_chain fn a b) w)` by
       metis_tac[frame_result_rel_terminates] >>
     drule run_blocks_terminates_mono >>
     disch_then (qspec_then `SUC j` mp_tac) >> simp[] >>
     disch_then SUBST1_TAC >> simp[]) >>
  `run_blocks (SUC j) C fn v = run_blocks j C fn u` by
    simp[run_blocks_unfold] >>
  irule scfg_chain_continue_forward_fuel >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise scfg_chain_runs_forward_fuel

Theorem scfg_chain_fn_bisim_fuel:
  scfg_chain_hyp fn a b ==> fn_bisim_fuel I fn (scfg_chain fn a b)
Proof
  strip_tac >> rewrite_tac[fn_bisim_fuel_def] >>
  `fn_entry_label (scfg_chain fn a b) = fn_entry_label fn` by
    metis_tac[scfg_chain_entry_eq] >>
  conj_tac >- simp[scfg_chain_def] >> conj_tac >- simp[] >>
  rpt strip_tac >> simp[] >>
  `scfg_chain_exit a b s s` by metis_tac[scfg_chain_initial_exit] >>
  `scfg_bprefix ctx fn s s /\ ~s.vs_halted` by
    fs[scfg_bprefix_rules, fn_entry_state_def] >>
  irule scfg_chain_runs_forward_fuel >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem scfg_chain_runs_forward:
  !n s r t. scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  run_blocks n C fn s = r /\ terminates r ==>
  ?k. frame_result_rel r (run_blocks k C (scfg_chain fn a b) t)
Proof
  rpt strip_tac >> qexists_tac `n` >>
  irule scfg_chain_runs_forward_fuel >> metis_tac[]
QED

Theorem scfg_chain_fn_bisim:
  scfg_chain_hyp fn a b ==> fn_bisim fn (scfg_chain fn a b)
Proof
  strip_tac >> rewrite_tac[fn_bisim_def] >>
  `fn_entry_label (scfg_chain fn a b) = fn_entry_label fn` by
    metis_tac[scfg_chain_entry_eq] >>
  conj_tac >- simp[scfg_chain_def] >> conj_tac >- simp[] >>
  rpt strip_tac >>
  `scfg_chain_exit a b s s` by metis_tac[scfg_chain_initial_exit] >>
  `scfg_bprefix ctx fn s s /\ ~s.vs_halted` by
    fs[scfg_bprefix_rules, fn_entry_state_def] >>
  FIRST [irule scfg_chain_runs_forward, irule scfg_chain_runs_backward] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
