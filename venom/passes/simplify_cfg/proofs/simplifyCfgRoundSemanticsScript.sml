(* Round and bounded-iteration composition. *)
Theory simplifyCfgRoundSemantics
Ancestors
  simplifyCfgCollapseSemantics simplifyCfgGeneratedSubst simplifyCfgCleanup
  simplifyCfgStaticInterface simplifyCfgSimTools simplifyCfgDefs venomWf
  cfgTransform venomInst list

Theorem scfg_cleanup_contract:
  scfg_static fn ==>
  scfg_collapse_contract fn (fix_all_phis (remove_unreachable_blocks fn))
Proof
  simp[scfg_collapse_contract_def] >> strip_tac >>
  metis_tac[scfg_normalized_cleanup, scfg_static_cleanup_entry,
            scfg_cleanup_bisim, scfg_cleanup_frame_sim_same, scfg_static_def]
QED

Theorem scfg_round_contract:
  scfg_static fn ==>
  scfg_collapse_contract fn (FST (simplify_cfg_round_with_labels fn))
Proof
  strip_tac >>
  Cases_on `fn_entry_label fn`
  >- (fs[scfg_static_def, wf_function_def, fn_has_entry_def,
         fn_entry_label_def, entry_block_def] >> Cases_on `fn.fn_blocks` >> gvs[]) >>
  qabbrev_tac `clean = fix_all_phis (remove_unreachable_blocks fn)` >>
  `scfg_collapse_contract fn clean` by
    metis_tac[scfg_cleanup_contract] >>
  `scfg_normalized clean` by fs[scfg_collapse_contract_def] >>
  Cases_on `collapse_dfs clean [] [] x` >> PairCases_on `r` >>
  `scfg_collapse_contract clean q` by metis_tac[scfg_collapse_joint, pairTheory.FST] >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  `ALL_DISTINCT (fn_labels clean)` by
    (fs[scfg_normalized_def, scfg_static_def, wf_function_def, fn_labels_def]) >>
  `subst_block_labels_fn r0 q = q` by metis_tac[scfg_collapse_subst_identity] >>
  `scfg_collapse_contract q (fix_all_phis (remove_unreachable_blocks q))` by
    metis_tac[scfg_cleanup_contract, scfg_normalized_static] >>
  Cases_on `r0 = []` >>
  gvs[simplify_cfg_round_with_labels_def, Abbr `clean`] >>
  metis_tac[scfg_collapse_contract_trans]
QED

Theorem scfg_iter_contract:
  !n fn. scfg_static fn ==>
    scfg_static (FST (simplify_cfg_iter_with_labels n fn)) /\
    fn_entry_label (FST (simplify_cfg_iter_with_labels n fn)) = fn_entry_label fn /\
    fn_bisim fn (FST (simplify_cfg_iter_with_labels n fn)) /\
    !C. frame_sim L C C fn (FST (simplify_cfg_iter_with_labels n fn))
Proof
  Induct
  >- (simp[simplify_cfg_iter_with_labels_def, fn_bisim_refl] >>
      rpt strip_tac >> irule frame_sim_ctx_bisim >>
      metis_tac[ctx_bisim_refl, scfg_static_inst_wf]) >>
  gen_tac >> disch_tac >> suspend "step"
QED

Resume scfg_iter_contract[step]:
  Cases_on `simplify_cfg_round_with_labels fn` >>
  `scfg_collapse_contract fn q` by metis_tac[scfg_round_contract, pairTheory.FST] >>
  Cases_on `q.fn_blocks = fn.fn_blocks`
  >- (simp[simplify_cfg_iter_with_labels_def, fn_bisim_refl] >>
      gen_tac >> irule frame_sim_ctx_bisim >>
      metis_tac[ctx_bisim_refl, scfg_static_inst_wf]) >>
  `scfg_static q` by
    metis_tac[scfg_collapse_contract_def, scfg_normalized_static] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  gvs[simplify_cfg_iter_with_labels_def, scfg_collapse_contract_def] >>
  metis_tac[fn_bisim_trans, frame_sim_trans]
QED
Finalise scfg_iter_contract
