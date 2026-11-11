Theory simplifyCfgCleanupGasEvents
Ancestors
  simplifyCfgRestrictionSemantics simplifyCfgRestriction simplifyCfgDefs gasEvents
  venomExecSemantics venomExecProofs venomWf cfgTransform o1PassLift
  list relation simplifyCfgFixupGasEvents simplifyCfgFixupSemantics
  simplifyCfgFragments simplifyCfgStruct

Theorem scfg_restriction_gas_events:
  !n C fn s.
    wf_function fn /\ fn_inst_wf fn /\ fn_reachable fn s.vs_current_bb ==>
    gas_events_blocks n C (remove_unreachable_blocks fn) s =
    gas_events_blocks n C fn s
Proof
  Induct_on `n` >- simp[gas_events_blocks_def] >> rpt strip_tac >>
  `lookup_block s.vs_current_bb (remove_unreachable_blocks fn).fn_blocks =
   lookup_block s.vs_current_bb fn.fn_blocks` by
    (irule scfg_restriction_lookup_reachable >> metis_tac[wf_function_def]) >>
  `(remove_unreachable_blocks fn).fn_name = fn.fn_name` by
    (Cases_on `fn_entry_label fn` >> simp[remove_unreachable_blocks_def]) >>
  pure_once_rewrite_tac[gas_events_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  Cases_on `exec_block n C bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `exec_block n C bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >>
  first_x_assum irule >> simp[] >>
  irule scfg_exec_block_reachable >> metis_tac[]
QED

Theorem scfg_restriction_entry_gas_events:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn s ==>
  gas_events_blocks n C (remove_unreachable_blocks fn) s =
  gas_events_blocks n C fn s /\
  run_blocks n C (remove_unreachable_blocks fn) s = run_blocks n C fn s
Proof
  strip_tac >>
  `fn_reachable fn s.vs_current_bb` by
    (gvs[fn_entry_state_def, fn_reachable_def] >>
     qexists_tac `s.vs_current_bb` >> simp[]) >>
  metis_tac[scfg_restriction_gas_events, scfg_restriction_runs]
QED

Theorem scfg_rooted_fix_all_phis_observation:
  !n C fn s0 s.
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s ==>
  gas_events_blocks n C (fix_all_phis fn) s = gas_events_blocks n C fn s /\
  run_blocks n C (fix_all_phis fn) s = run_blocks n C fn s
Proof
  Induct_on `n` >- simp[gas_events_blocks_def, run_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >>
      simp[scfg_fix_all_phis_lookup]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  drule_all scfg_rooted_fix_phis_observation >>
  disch_then (qspecl_then [`fn.fn_name`, `n`] strip_assume_tac) >>
  `!t. run_block n C bb s = OK t /\ ~t.vs_halted ==>
    gas_events_blocks n C (fix_all_phis fn) t = gas_events_blocks n C fn t /\
    run_blocks n C (fix_all_phis fn) t = run_blocks n C fn t` by
    (gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
     qexists_tac `s0` >> simp[] >>
     irule scfg_bprefix_trans >> qexists_tac `s` >> simp[] >>
     irule scfg_bprefix_single >> metis_tac[]) >>
  reverse conj_tac
  >- (pure_once_rewrite_tac[run_blocks_unfold] >>
      simp[scfg_fix_all_phis_lookup] >>
      Cases_on `run_block n C bb s` >> simp[] >>
      rename1 `run_block n C bb s = OK t` >>
      Cases_on `t.vs_halted` >> simp[]) >>
  pure_once_rewrite_tac[gas_events_blocks_def] >>
  `(fix_all_phis fn).fn_name = fn.fn_name` by simp[fix_all_phis_def] >>
  simp[scfg_fix_all_phis_lookup] >>
  qpat_x_assum `run_block n C _ s = run_block n C bb s` mp_tac >>
  qspec_then `s` (qspec_then `bb.bb_instructions` strip_assume_tac)
    eval_phis_ok_or_error_defs >>
  qspec_then `s` (qspec_then
    `(fix_phis_in_block (pred_labels fn bb.bb_label) bb).bb_instructions`
    strip_assume_tac) eval_phis_ok_or_error_defs >>
  pure_asm_rewrite_tac[run_block_def] >> disch_tac >>
  qpat_x_assum `(case eval_phis _ _ of OK z => _ | _ => _ | _ => _ | _ => _ | _ => _) = _` mp_tac >>
  pure_asm_rewrite_tac[] >> strip_tac >> fs[] >>
  Cases_on `run_block_non_phis n C bb
    (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> fs[] >>
  rename1 `run_block_non_phis n C bb _ = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >>
  qpat_x_assum `!t. run_block_entry _ _ _ _ = OK t /\ _ ==> _`
    (qspec_then `t` mp_tac) >> simp[run_block_def]
QED

Theorem scfg_cleanup_entry_observation:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  fn_entry_state fn s ==>
  gas_events_blocks n C (fix_all_phis (remove_unreachable_blocks fn)) s =
    gas_events_blocks n C fn s /\
  run_blocks n C (fix_all_phis (remove_unreachable_blocks fn)) s =
    run_blocks n C fn s
Proof
  strip_tac >>
  `wf_function (remove_unreachable_blocks fn)` by
    metis_tac[remove_unreachable_blocks_wf] >>
  `fn_inst_wf (remove_unreachable_blocks fn)` by
    metis_tac[remove_unreachable_blocks_fn_inst_wf] >>
  `simplify_cfg_fn_ok (remove_unreachable_blocks fn)` by
    metis_tac[scfg_restriction_ok] >>
  `fn_entry_state (remove_unreachable_blocks fn) s` by
    metis_tac[scfg_restriction_entry_state] >>
  `!b. MEM b (remove_unreachable_blocks fn).fn_blocks ==>
    fn_reachable (remove_unreachable_blocks fn) b.bb_label` by
    (rpt strip_tac >> irule scfg_restriction_blocks_reachable >>
     gvs[wf_function_def, fn_entry_state_def] >> metis_tac[]) >>
  `scfg_bprefix C (remove_unreachable_blocks fn) s s` by
    simp[scfg_bprefix_refl] >>
  drule_all scfg_rooted_fix_all_phis_observation >> strip_tac >>
  simp[] >> irule scfg_restriction_entry_gas_events >> simp[]
QED
