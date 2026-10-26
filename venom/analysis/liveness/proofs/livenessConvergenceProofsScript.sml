Theory livenessConvergenceProofs
Ancestors
  livenessTerminationProofs cfgAnalysisProps
Libs
  listTheory pred_setTheory pairTheory
  livenessDefsTheory livenessBlockProofsTheory livenessTransferProofsTheory
  livenessInvariantProofsTheory worklistDefsTheory dfAnalyzeDefsTheory

Theorem lv_out_cong:
  (!s. MEM s (cfg_succs_of cfg l) ==>
       set (df_at [] st s 0) = set (df_at [] st' s 0)) ==>
  set (liveness_out bbs cfg l st) = set (liveness_out bbs cfg l st')
Proof
  strip_tac >> simp[liveness_out_def] >>
  irule SUBSET_ANTISYM >> conj_tac >>
  irule foldl_list_union_mono >> simp[] >> rpt strip_tac >>
  simp[EL_MAP] >> irule liveness_edge_transfer_mono >>
  metis_tac[MEM_EL, SUBSET_REFL]
QED

Theorem lv_out_block_unchanged:
  (~MEM h (cfg_succs_of cfg l) \/
   ~liveness_changed bbs h st (liveness_block bbs cfg h st)) ==>
  set (liveness_out bbs cfg l (liveness_block bbs cfg h st)) =
  set (liveness_out bbs cfg l st)
Proof
  strip_tac >> irule lv_out_cong >> rpt strip_tac >>
  Cases_on `s = h` >> gvs[liveness_block_other_inst] >>
  gvs[liveness_changed_def, same_vars_set]
QED

Definition lv_queue_consistent_def:
  lv_queue_consistent bbs cfg reachable wl st <=>
    !l. l IN reachable /\ ~MEM l wl ==>
      set (df_at [] st l (LENGTH (liveness_instrs bbs l))) =
      set (liveness_out bbs cfg l st)
End

Theorem lv_queue_initial:
  lv_queue_consistent bbs cfg (set wl) wl st
Proof
  simp[lv_queue_consistent_def]
QED

Theorem lv_queue_step:
  (!l s. MEM s (cfg_succs_of cfg l) <=> MEM l (cfg_preds_of cfg s)) /\
  lv_queue_consistent bbs cfg reachable (h::t) st ==>
  lv_queue_consistent bbs cfg reachable
    (FST (wl_step (liveness_changed bbs) (liveness_block bbs cfg)
                  (cfg_preds_of cfg) (h::t,st)))
    (SND (wl_step (liveness_changed bbs) (liveness_block bbs cfg)
                  (cfg_preds_of cfg) (h::t,st)))
Proof
  strip_tac >>
  Cases_on `liveness_changed bbs h st (liveness_block bbs cfg h st)` >>
  simp[wl_step_def, lv_queue_consistent_def] >> rpt strip_tac >>
  `set (liveness_out bbs cfg l (liveness_block bbs cfg h st)) =
   set (liveness_out bbs cfg l st)` by
    (irule lv_out_block_unchanged >> metis_tac[MEM_APPEND]) >>
  Cases_on `l = h` >> gvs[liveness_block_exit, liveness_block_other_inst] >>
  gvs[lv_queue_consistent_def] >> metis_tac[MEM, MEM_APPEND]
QED

Theorem liveness_recompute_queue_consistent:
  wf_function fn ==>
  lv_queue_consistent fn.fn_blocks (cfg_analyze fn)
    {l | cfg_reachable_of (cfg_analyze fn) l}
    (FST (wl_iterate (liveness_changed fn.fn_blocks)
       (liveness_block fn.fn_blocks (cfg_analyze fn))
       (cfg_preds_of (cfg_analyze fn)) (cfg_analyze fn).cfg_dfs_post
       (init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks))))
    (liveness_recompute fn)
Proof
  strip_tac >> simp[liveness_recompute_def] >>
  irule (liveness_recompute_lift |> Q.INST
    [`Q` |-> `\p. lv_queue_consistent fn.fn_blocks (cfg_analyze fn)
      {l | cfg_reachable_of (cfg_analyze fn) l} (FST p) (SND p)`]
    |> BETA_RULE) >> reverse conj_tac
  >- (drule cfg_analyze_reachable_sets >>
      simp[lv_queue_consistent_def, EXTENSION] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `p` >> Cases_on `q` >> gvs[] >>
  irule lv_queue_step >> simp[cfg_edge_symmetry_uncond]
QED

Theorem liveness_recompute_convergence:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl ==>
  same_vars
    (df_at [] (liveness_recompute fn) lbl
       (LENGTH (liveness_instrs fn.fn_blocks lbl)))
    (liveness_out fn.fn_blocks (cfg_analyze fn) lbl (liveness_recompute fn))
Proof
  strip_tac >> drule liveness_recompute_queue_consistent >>
  simp[liveness_recompute_queue_empty, lv_queue_consistent_def, same_vars_set]
QED

Theorem liveness_out_edge_subset:
  MEM succ (cfg_succs_of cfg lbl) ==>
  set (liveness_edge_transfer bbs succ lbl (df_at [] st succ 0)) SUBSET
  set (liveness_out bbs cfg lbl st)
Proof
  simp[liveness_out_def, SUBSET_DEF, mem_foldl_list_union, MEM_MAP] >>
  metis_tac[]
QED

Theorem liveness_recompute_edge_subset:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl /\
  MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
  set (liveness_edge_transfer fn.fn_blocks succ lbl
         (df_at [] (liveness_recompute fn) succ 0)) SUBSET
  set (df_at [] (liveness_recompute fn) lbl
         (LENGTH (liveness_instrs fn.fn_blocks lbl)))
Proof
  strip_tac >> drule_all liveness_recompute_convergence >>
  simp[same_vars_set] >> strip_tac >>
  asm_rewrite_tac[] >> irule liveness_out_edge_subset >> simp[]
QED
