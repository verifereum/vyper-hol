Theory makeSsaCurrentDominanceBridge
Ancestors
  makeSsaCurrentAnalysis dominatorProofs dominatorDefs venomWf venomInst
  relation list

Theorem current_lrc_fn_path:
  !ls a y. LRC (fn_cfg_edge fn) ls a y ==>
    is_fn_path fn (ls ++ [y]) /\
    HD (ls ++ [y]) = a /\ LAST (ls ++ [y]) = y
Proof
  Induct >> simp[LRC_def, is_fn_path_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `ls` >> gvs[is_fn_path_def, LAST_CONS_cond, LAST_APPEND_CONS]
QED

Theorem current_semantic_dominates:
  wf_function fn /\ MEM d (fn_labels fn) /\ fn_dominates fn d y ==>
  dominates (dom_analyze (cfg_analyze fn) fn) d y
Proof
  strip_tac >>
  `fn_reachable fn y` by gvs[fn_dominates_def] >>
  `?bb. entry_block fn = SOME bb` by
    (Cases_on `entry_block fn` >>
     gvs[fn_reachable_def, fn_entry_label_def]) >>
  simp[dominates_def] >> irule on_every_path_dom >>
  simp[current_cfg_reachable] >>
  ` (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) = fn_cfg_edge fn` by
    simp[FUN_EQ_THM, current_cfg_edge_succs] >>
  simp[] >> rpt strip_tac >>
  drule current_lrc_fn_path >> strip_tac >>
  qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  simp[fn_dominates_def] >> strip_tac >>
  first_x_assum (qspec_then `ls ++ [y]` mp_tac) >>
  simp[fn_entry_label_def] >> metis_tac[]
QED
