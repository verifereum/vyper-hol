Theory concretizePtrHistoryCfg
Ancestors
  cfgCorrectnessProof
  concretizePtrHistoryUsed cfgAnalysisProps cfgWf codegenReadyCompute
  venomExecProps venomExecSemantics venomWf venomInst list pred_set

Theorem ptr_history_cfg_analyze_ok:
  wf_function fn /\ all_reachable fn ==>
  ptr_history_cfg_ok fn (cfg_analyze fn)
Proof
  strip_tac >> simp[ptr_history_cfg_ok_def] >> conj_tac
  >- (rpt strip_tac >>
      `bb.bb_instructions <> []` by
        metis_tac[wf_function_def, bb_well_formed_def] >>
      `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
        (gvs[GSYM fn_reachable_cfg_analyze, all_reachable_def]) >>
      drule cfg_analyze_reachable_sets >>
      fs[EXTENSION, lookup_block_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[fn_cfg_edge_def] >>
  drule_all cfg_analyze_preserves_bb_succs >> strip_tac >>
  metis_tac[cfg_edge_symmetry_uncond]
QED
