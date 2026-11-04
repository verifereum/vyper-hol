Theory concretizeAnalysisLivenessProduction
Ancestors concretizeAnalysisLivenessClosure concretizeMemLocDefs cfgAnalysisProps cfgWf
  codegenReadyCompute venomWf list pred_set

Theorem ml_cfg_production_coverage:
  wf_function fn /\ all_reachable fn /\ MEM bb fn.fn_blocks ==>
  MEM bb.bb_label (cfg_analyze fn).cfg_dfs_post /\
  MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    gvs[GSYM fn_reachable_cfg_analyze, all_reachable_def] >>
  drule cfg_analyze_reachable_sets >> simp[EXTENSION] >> metis_tac[]
QED

Theorem ml_production_saturated:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  ml_one_pass bpr mems sizes pallocas (cfg_analyze fn) fn la us =
    (changed,la',us') ==>
  (!addr. MEM a (ml_lookup la' addr) <=> MEM a (ml_lookup la addr)) /\
  (!addr. MEM a (ml_lookup us' addr) <=> MEM a (ml_lookup us addr))
Proof
  strip_tac >> irule ml_iterate_fuel_saturated >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists `concretize_memloc_fuel fn` >> simp[] >>
  conj_tac >- metis_tac[ml_cfg_production_coverage] >>
  simp[concretize_memloc_fuel_def]
QED
