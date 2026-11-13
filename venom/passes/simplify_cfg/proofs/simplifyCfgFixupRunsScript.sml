(* Whole-run transport for PHI fixup after unreachable restriction. *)
Theory simplifyCfgFixupRuns
Ancestors
  simplifyCfgFixupSemantics simplifyCfgFragments simplifyCfgDefs
  venomExecSemantics o1PassLift venomWf simplifyCfgSimTools
  simplifyCfgFixupStatic contextCodegenRel passSimulationDefs
  simplifyCfgStruct

Theorem scfg_fix_all_phis_runs_forward_same_fuel:
  !n s r. wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\ (!e. r <> Error e) /\
  run_blocks n C fn s = r ==>
  run_blocks n C (fix_all_phis fn) s = r
Proof
  Induct_on `n` >- simp[Once run_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `run_block n C bb s` >> simp[] >> strip_tac
  >- (`run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s = OK v` by
        (irule scfg_rooted_fix_phis_run_block_same_fuel >> simp[] >> metis_tac[]) >>
      Cases_on `v.vs_halted`
      >- gvs[run_blocks_unfold, scfg_fix_all_phis_lookup] >>
      `scfg_bprefix C fn s0 v` by
        metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
      `run_blocks n C (fix_all_phis fn) v = r` by
        (first_x_assum irule >> gvs[]) >>
      simp[run_blocks_unfold, scfg_fix_all_phis_lookup]) >>
  gvs[] >>
  `run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s =
       run_block n C bb s` by
    (irule scfg_rooted_fix_phis_run_block_same_fuel >> simp[] >> metis_tac[]) >>
  simp[run_blocks_unfold, scfg_fix_all_phis_lookup] >>
  Cases_on `run_block n C bb s` >> gvs[]
QED

Theorem scfg_fix_all_phis_runs_forward:
  !n s r. wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\ (!e. r <> Error e) /\
  run_blocks n C fn s = r ==>
  ?m. run_blocks m C (fix_all_phis fn) s = r
Proof
  metis_tac[scfg_fix_all_phis_runs_forward_same_fuel]
QED

Theorem scfg_fix_all_phis_runs_backward:
  !n s r. wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\ (!e. r <> Error e) /\
  run_blocks n C (fix_all_phis fn) s = r ==>
  ?m. run_blocks m C fn s = r
Proof
  Induct_on `n` >- simp[Once run_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_blocks_unfold, scfg_fix_all_phis_lookup] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s` >>
  simp[] >> strip_tac
  >- (`?k. run_block k C bb s = OK v` by
        (irule scfg_rooted_fix_phis_run_block_back >> simp[] >> metis_tac[]) >>
      Cases_on `v.vs_halted`
      >- (qexists_tac `SUC k` >> gvs[run_blocks_unfold]) >>
      `scfg_bprefix C fn s0 v` by
        metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
      `?m. run_blocks m C fn v = r` by
        (first_x_assum irule >> gvs[]) >>
      irule scfg_bstep_continue >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `?k. run_block k C bb s =
       run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s` by
    (irule scfg_rooted_fix_phis_run_block_back >> simp[] >> metis_tac[]) >>
  qexists_tac `SUC k` >> simp[run_blocks_unfold] >>
  Cases_on `run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s` >>
  gvs[]
QED

Theorem scfg_fix_all_phis_entry_runs_forward_same_fuel:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s /\ (!e. r <> Error e) /\ run_blocks n C fn s = r ==>
  run_blocks n C (fix_all_phis fn) s = r
Proof
  rpt strip_tac >> irule scfg_fix_all_phis_runs_forward_same_fuel >>
  simp[] >> metis_tac[scfg_bprefix_rules]
QED

Theorem scfg_fix_all_phis_entry_runs_forward:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s /\ (!e. r <> Error e) /\ run_blocks n C fn s = r ==>
  ?m. run_blocks m C (fix_all_phis fn) s = r
Proof
  rpt strip_tac >> irule scfg_fix_all_phis_runs_forward >>
  simp[] >> metis_tac[scfg_bprefix_rules]
QED

Theorem scfg_fix_all_phis_entry_runs_backward:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s /\ (!e. r <> Error e) /\
  run_blocks n C (fix_all_phis fn) s = r ==>
  ?m. run_blocks m C fn s = r
Proof
  rpt strip_tac >> irule scfg_fix_all_phis_runs_backward >>
  simp[] >> metis_tac[scfg_bprefix_rules]
QED

Theorem scfg_fix_all_phis_bprefix_backward:
  !C fn a t. scfg_bprefix C (fix_all_phis fn) a t ==>
  !s0. wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 a ==>
  scfg_bprefix C fn s0 t
Proof
  rpt gen_tac >>
  Induct_on `scfg_bprefix C (fix_all_phis fn) a t` >>
  rpt strip_tac >> gvs[scfg_fix_all_phis_lookup] >>
  Cases_on `lookup_block a.vs_current_bb fn.fn_blocks` >> gvs[] >>
  rename1 `lookup_block _ _ = SOME b` >>
  rename1 `run_block _ _ _ _ = OK u` >>
  `?n. run_block n C b a = OK u` by
    (irule scfg_rooted_fix_phis_run_block_back >> simp[] >> metis_tac[]) >>
  `scfg_bprefix C fn s0 u` by
    metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
  first_x_assum irule >> simp[]
QED

Theorem scfg_fix_all_phis_bisim:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) ==>
  fn_bisim fn (fix_all_phis fn)
Proof
  strip_tac >>
  `(fix_all_phis fn).fn_name = fn.fn_name` by simp[fix_all_phis_def] >>
  simp[fn_bisim_def, fix_all_phis_entry] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qx_gen_tac `n` >> strip_tac >>
      `!e. run_blocks n ctx fn s <> Error e` by
        (Cases_on `run_blocks n ctx fn s` >> fs[terminates_def]) >>
      `?m. run_blocks m ctx (fix_all_phis fn) s = run_blocks n ctx fn s` by
        (irule scfg_fix_all_phis_entry_runs_forward >> simp[] >> metis_tac[]) >>
      qexists_tac `m` >> simp[run_blocks_frame_result_refl]) >>
  qx_gen_tac `n` >> strip_tac >>
  `!e. run_blocks n ctx (fix_all_phis fn) s <> Error e` by
    (Cases_on `run_blocks n ctx (fix_all_phis fn) s` >> fs[terminates_def]) >>
  `?m. run_blocks m ctx fn s = run_blocks n ctx (fix_all_phis fn) s` by
    (irule scfg_fix_all_phis_entry_runs_backward >> simp[] >> metis_tac[]) >>
  qexists_tac `m` >> simp[run_blocks_frame_result_refl]
QED
