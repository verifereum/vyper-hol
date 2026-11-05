Theory simplifyCfgReach
Ancestors
  simplifyCfgStruct simplifyCfgDefs cfgWf venomWf venomInst

Theorem all_reachable_blocks_cong:
  f.fn_blocks = g.fn_blocks ==> (all_reachable f <=> all_reachable g)
Proof
  strip_tac >>
  `fn_cfg_edge f = fn_cfg_edge g` by
    simp[FUN_EQ_THM, fn_cfg_edge_def] >>
  simp[all_reachable_def, fn_reachable_def, fn_entry_label_def,
       entry_block_def]
QED

Theorem simplify_cfg_iter_with_labels_reachable:
  !n fn. wf_function fn /\ (n = 0 ==> all_reachable fn) ==>
    all_reachable (FST (simplify_cfg_iter_with_labels n fn))
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt strip_tac >>
  Cases_on `simplify_cfg_round_with_labels fn` >>
  rename1 `simplify_cfg_round_with_labels fn = (next, labels)` >>
  `wf_function next` by
    (drule simplify_cfg_round_wf >> simp[simplify_cfg_round_def]) >>
  `all_reachable next` by
    (qpat_assum `wf_function fn` mp_tac >>
     disch_then (mp_tac o MATCH_MP simplify_cfg_round_reachable) >>
     simp[simplify_cfg_round_def]) >>
  simp[Once simplify_cfg_iter_with_labels_def] >>
  Cases_on `next.fn_blocks = fn.fn_blocks`
  >- (simp[] >> drule all_reachable_blocks_cong >> simp[]) >>
  simp[] >>
  Cases_on `simplify_cfg_iter_with_labels n next` >>
  gvs[] >> first_x_assum (qspec_then `next` mp_tac) >> simp[]
QED
