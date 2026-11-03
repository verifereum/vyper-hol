Theory simplifyCfgReach
Ancestors
  simplifyCfgStruct cfgWf venomWf venomInst

Theorem all_reachable_blocks_cong:
  f.fn_blocks = g.fn_blocks ==> (all_reachable f <=> all_reachable g)
Proof
  strip_tac >>
  `fn_cfg_edge f = fn_cfg_edge g` by
    simp[FUN_EQ_THM, fn_cfg_edge_def] >>
  simp[all_reachable_def, fn_reachable_def, fn_entry_label_def,
       entry_block_def]
QED
