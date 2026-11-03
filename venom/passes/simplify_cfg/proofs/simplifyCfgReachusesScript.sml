Theory simplifyCfgReachuses
Ancestors
  simplifyCfgDefs simplifyCfgStruct simplifyCfgPhiRepair
  simplifyCfgDataflow simplifyCfgRepairDataflow simplifyCfgPhiPreds
  simplifyCfgChainDataflow simplifyCfgBypassDataflow
  venomWf cfgTransform list rich_list

Theorem fix_phi_inst_inst_wf:
  inst_wf inst ==> inst_wf (fix_phi_inst actual_preds inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- ( `LENGTH inst.inst_outputs = 1 /\ phi_well_formed inst.inst_operands` by
         fs[inst_wf_def] >>
       `phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)` by
         simp[filter_phi_ops_well_formed] >>
       simp[fix_phi_inst_def] >>
       Cases_on `filter_phi_ops actual_preds inst.inst_operands` >>
       simp[inst_wf_def] >>
       Cases_on `t` >> simp[inst_wf_def] >>
       Cases_on `t'` >> simp[inst_wf_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem fix_all_phis_fn_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (fix_all_phis fn)
Proof
  simp[fn_inst_wf_def, fix_all_phis_def, fix_phis_in_block_def,
       MEM_MAP, MEM_APPEND, MEM_FILTER, PULL_EXISTS] >>
  metis_tac[fix_phi_inst_inst_wf]
QED

Theorem remove_unreachable_blocks_fn_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (remove_unreachable_blocks fn)
Proof
  simp[fn_inst_wf_def, remove_unreachable_blocks_def] >>
  Cases_on `fn_entry_label fn` >> simp[MEM_FILTER] >> metis_tac[]
QED

Theorem repair_reachable_invariants:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn ==>
  wf_function (fix_all_phis (remove_unreachable_blocks fn)) /\
  fn_inst_wf (fix_all_phis (remove_unreachable_blocks fn)) /\
  first_block_no_preds (fix_all_phis (remove_unreachable_blocks fn)) /\
  scfg_phi_safe (fix_all_phis (remove_unreachable_blocks fn)) /\
  fn_defs_reach_uses (fix_all_phis (remove_unreachable_blocks fn)) /\
  scfg_phi_preds (fix_all_phis (remove_unreachable_blocks fn)) /\
  all_reachable (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >>
  `wf_function (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_wf] >>
  `fn_inst_wf (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_fn_inst_wf] >>
  `first_block_no_preds (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_first_block_no_preds] >>
  `scfg_phi_safe (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_phi_safe] >>
  `fn_defs_reach_uses (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_defs_reach_uses] >>
  `all_reachable (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_reachable] >>
  simp[fix_all_phis_wf, fix_all_phis_fn_inst_wf,
       fix_all_phis_first_block_no_preds, fix_all_phis_phi_safe,
       fix_all_phis_defs_reach_uses, fix_all_phis_phi_preds,
       fix_all_phis_all_reachable]
QED
