Theory livenessTerminationProofs
Ancestors
  livenessRankProofs livenessWorklistProofs
Libs
  listTheory pairTheory arithmeticTheory pred_setTheory
  livenessDefsTheory livenessInvariantProofsTheory worklistDefsTheory

(* The rank and its finite universe are hidden behind this transport rule. *)
Theorem lv_iteration_rule:
  lv_inv bbs cfg st /\ EVERY (\l. l IN lv_labels cfg) wl /\ Q (wl,st) /\
  (!p. lv_inv bbs cfg (SND p) /\
       EVERY (\l. l IN lv_labels cfg) (FST p) /\ Q p /\ FST p <> [] ==>
       Q (wl_step (liveness_changed bbs) (liveness_block bbs cfg)
                  (cfg_preds_of cfg) p)) ==>
  lv_inv bbs cfg
    (SND (wl_iterate (liveness_changed bbs) (liveness_block bbs cfg)
                    (cfg_preds_of cfg) wl st)) /\
  EVERY (\l. l IN lv_labels cfg)
    (FST (wl_iterate (liveness_changed bbs) (liveness_block bbs cfg)
                    (cfg_preds_of cfg) wl st)) /\
  Q (wl_iterate (liveness_changed bbs) (liveness_block bbs cfg)
                (cfg_preds_of cfg) wl st) /\
  FST (wl_iterate (liveness_changed bbs) (liveness_block bbs cfg)
                 (cfg_preds_of cfg) wl st) = []
Proof
  strip_tac >> irule wl_changed_iterate >>
  simp[lv_labels_preds] >>
  qexistsl_tac [`2 * CARD (lv_labels cfg) * CARD (set (fn_all_vars bbs))`,
                `lv_rank bbs (lv_labels cfg)`] >>
  simp[lv_labels_finite, lv_inv_block, lv_rank_mono, lv_rank_strict, lv_rank_bound] >>
  rpt strip_tac >>
  `2 * (CARD (set (fn_all_vars bbs)) * CARD (lv_labels cfg)) =
   2 * CARD (lv_labels cfg) * CARD (set (fn_all_vars bbs))` by
    (pure_rewrite_tac[GSYM MULT_ASSOC] >> AP_TERM_TAC >>
     MATCH_ACCEPT_TAC MULT_COMM) >>
  asm_rewrite_tac[] >> irule lv_rank_bound >> simp[lv_labels_finite] >> metis_tac[]
QED

Theorem lv_finite_exhaustion:
  lv_inv bbs cfg st /\ EVERY (\l. l IN lv_labels cfg) wl ==>
  ?n. FST (FUNPOW (wl_step (liveness_changed bbs) (liveness_block bbs cfg)
                           (cfg_preds_of cfg)) n (wl,st)) = []
Proof
  strip_tac >> irule wl_changed_terminates >>
  qexistsl_tac [`\s. lv_inv bbs cfg s`,
                `2 * CARD (lv_labels cfg) * CARD (set (fn_all_vars bbs))`,
                `lv_rank bbs (lv_labels cfg)`, `\l. l IN lv_labels cfg`] >>
  simp[lv_labels_finite, lv_labels_preds, lv_inv_block, lv_rank_mono,
       lv_rank_strict] >>
  rpt strip_tac >>
  `2 * (CARD (set (fn_all_vars bbs)) * CARD (lv_labels cfg)) =
   2 * CARD (lv_labels cfg) * CARD (set (fn_all_vars bbs))` by
    (pure_rewrite_tac[GSYM MULT_ASSOC] >> AP_TERM_TAC >>
     MATCH_ACCEPT_TAC MULT_COMM) >>
  asm_rewrite_tac[] >> irule lv_rank_bound >> simp[lv_labels_finite] >> metis_tac[]
QED

Theorem lv_fuel_preserves:
  lv_inv bbs cfg st ==>
  !fuel wl. lv_inv bbs cfg
    (SND (wl_iterate_fuel fuel (liveness_changed bbs) (liveness_block bbs cfg)
                          (cfg_preds_of cfg) wl st))
Proof
  qid_spec_tac `st` >>
  `!fuel wl st. lv_inv bbs cfg st ==> lv_inv bbs cfg
    (SND (wl_iterate_fuel fuel (liveness_changed bbs) (liveness_block bbs cfg)
                          (cfg_preds_of cfg) wl st))` suffices_by metis_tac[] >>
  Induct >> simp[wl_iterate_fuel_def] >> rpt strip_tac >> Cases_on `wl` >>
  simp[wl_iterate_fuel_def] >>
  Cases_on `liveness_changed bbs h st (liveness_block bbs cfg h st)` >>
  simp[wl_step_def, lv_inv_block]
QED

Theorem liveness_recompute_invariant:
  lv_inv fn.fn_blocks (cfg_analyze fn) (liveness_recompute fn)
Proof
  simp[liveness_recompute_def] >>
  irule (lv_iteration_rule |> Q.INST [`Q` |-> `\p. T`] |> SRULE [] |> cj 1) >>
  simp[lv_inv_init, lv_labels_initial]
QED

Theorem liveness_recompute_fuel_invariant:
  lv_inv fn.fn_blocks (cfg_analyze fn) (liveness_recompute_fuel fuel fn)
Proof
  simp[liveness_recompute_fuel_def] >> irule lv_fuel_preserves >> simp[lv_inv_init]
QED

Theorem liveness_recompute_fuel_agreement:
  ?fuel. liveness_recompute_fuel fuel fn = liveness_recompute fn
Proof
  simp[liveness_recompute_fuel_def, liveness_recompute_def] >>
  `?fuel. wl_iterate_fuel fuel (liveness_changed fn.fn_blocks)
      (liveness_block fn.fn_blocks (cfg_analyze fn)) (cfg_preds_of (cfg_analyze fn))
      (cfg_analyze fn).cfg_dfs_post
      (init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks)) =
    wl_iterate (liveness_changed fn.fn_blocks)
      (liveness_block fn.fn_blocks (cfg_analyze fn)) (cfg_preds_of (cfg_analyze fn))
      (cfg_analyze fn).cfg_dfs_post
      (init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks))` by
    (irule wl_exhaustion_fuel_agreement >> irule lv_finite_exhaustion >>
     simp[lv_inv_init, lv_labels_initial]) >> metis_tac[]
QED

(* Consumer boundary: neither rank instantiation nor WHILE reasoning is needed. *)
Theorem liveness_recompute_lift:
  Q ((cfg_analyze fn).cfg_dfs_post,
     init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks)) /\
  (!p. lv_inv fn.fn_blocks (cfg_analyze fn) (SND p) /\
       EVERY (\l. l IN lv_labels (cfg_analyze fn)) (FST p) /\
       Q p /\ FST p <> [] ==>
       Q (wl_step (liveness_changed fn.fn_blocks)
            (liveness_block fn.fn_blocks (cfg_analyze fn))
            (cfg_preds_of (cfg_analyze fn)) p)) ==>
  Q (wl_iterate (liveness_changed fn.fn_blocks)
       (liveness_block fn.fn_blocks (cfg_analyze fn))
       (cfg_preds_of (cfg_analyze fn)) (cfg_analyze fn).cfg_dfs_post
       (init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks)))
Proof
  strip_tac >> irule (cj 3 lv_iteration_rule) >>
  simp[lv_inv_init, lv_labels_initial]
QED

Theorem liveness_recompute_queue_empty:
  FST (wl_iterate (liveness_changed fn.fn_blocks)
       (liveness_block fn.fn_blocks (cfg_analyze fn))
       (cfg_preds_of (cfg_analyze fn)) (cfg_analyze fn).cfg_dfs_post
       (init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks))) = []
Proof
  irule (lv_iteration_rule |> Q.INST [`Q` |-> `\p. T`] |> SRULE [] |> cj 3) >>
  simp[lv_inv_init, lv_labels_initial]
QED

Theorem liveness_recompute_finite_exhaustion:
  ?n. FST (FUNPOW (wl_step (liveness_changed fn.fn_blocks)
       (liveness_block fn.fn_blocks (cfg_analyze fn))
       (cfg_preds_of (cfg_analyze fn))) n
       ((cfg_analyze fn).cfg_dfs_post,
        init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks))) = []
Proof
  irule lv_finite_exhaustion >> simp[lv_inv_init, lv_labels_initial]
QED
