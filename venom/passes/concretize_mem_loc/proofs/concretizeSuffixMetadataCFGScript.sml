Theory concretizeSuffixMetadataCFG
Ancestors
  cfgNormDefs simplifyCfgDefs venomInst list

Theorem insert_split_supply_mems_used[local]:
  insert_split_supply s fn pred target = (out,s') ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[insert_split_supply_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem find_and_split_supply_mems_used[local]:
  !bbs fn s out changed s'.
    find_and_split_supply fn s bbs = (out,changed,s') ==>
    out.fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[find_and_split_supply_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[insert_split_supply_mems_used]
QED

Theorem cfg_norm_iter_supply_mems_used[local]:
  !n s fn out s'. cfg_norm_iter_supply n s fn = (out,s') ==>
    out.fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[cfg_norm_iter_supply_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  metis_tac[find_and_split_supply_mems_used, cfg_norm_round_supply_def]
QED

Theorem cfg_norm_function_supply_mems_used:
  cfg_norm_function_supply s fn = (out,s') ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_mems_used]
QED

Theorem do_merge_jump_mems_used[local]:
  do_merge_jump fn a b lm = SOME (out,lm') ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[do_merge_jump_def] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem try_bypass_mems_used[local]:
  !succs fn lm bb out lm' changed.
    try_bypass fn lm bb succs = (out,lm',changed) ==>
    out.fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[try_bypass_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[do_merge_jump_mems_used]
QED

Theorem collapse_mems_used_joint[local]:
  (!fn lm vis lbl.
    (FST (collapse_dfs fn lm vis lbl)).fn_mems_used = fn.fn_mems_used) /\
  (!fn lm vis succs.
    (FST (collapse_dfs_succs fn lm vis succs)).fn_mems_used = fn.fn_mems_used)
Proof
  ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- simp[Once collapse_dfs_def]
  >> suspend "succs"
QED

Resume collapse_mems_used_joint[dfs]:
  rpt strip_tac >>
  simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- simp[] >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  Cases_on `bb_succs bb`
  >- (Cases_on `MEM lbl vis` >> gvs[try_bypass_def]) >>
  Cases_on `t`
  >- (Cases_on `lookup_block h fn.fn_blocks`
      >- (Cases_on `MEM lbl vis` >> simp[]) >>
      rename1 `lookup_block h fn.fn_blocks = SOME next_bb` >>
      Cases_on `can_merge_blocks fn bb next_bb`
      >- gvs[] >>
      Cases_on `MEM lbl vis` >> gvs[]) >>
  Cases_on `try_bypass fn lm bb (h::h'::t')` >>
  PairCases_on `r` >> Cases_on `r1` >> gvs[] >>
  `q.fn_mems_used = fn.fn_mems_used` by
    metis_tac[try_bypass_mems_used] >>
  Cases_on `MEM lbl vis` >> gvs[]
QED

Resume collapse_mems_used_joint[succs]:
  rpt strip_tac >> simp[Once collapse_dfs_def] >>
  Cases_on `collapse_dfs fn lm vis lbl` >>
  PairCases_on `r` >> gvs[]
QED

Finalise collapse_mems_used_joint

Theorem cfg_cleanup_mems_used[local]:
  (remove_unreachable_blocks fn).fn_mems_used = fn.fn_mems_used /\
  (fix_all_phis fn).fn_mems_used = fn.fn_mems_used /\
  (subst_block_labels_fn lm fn).fn_mems_used = fn.fn_mems_used
Proof
  simp[remove_unreachable_blocks_def, fix_all_phis_def,
       cfgTransformTheory.subst_block_labels_fn_def] >>
  Cases_on `fn_entry_label fn` >> simp[]
QED

Theorem simplify_cfg_round_with_labels_mems_used[local]:
  simplify_cfg_round_with_labels fn = (out,lm) ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[simplify_cfg_round_with_labels_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), cfg_cleanup_mems_used] >>
  pairarg_tac >> gvs[cfg_cleanup_mems_used] >>
  Cases_on `label_map = []` >> gvs[cfg_cleanup_mems_used] >>
  metis_tac[CONJUNCT1 collapse_mems_used_joint, pairTheory.FST,
            cfg_cleanup_mems_used]
QED

Theorem simplify_cfg_iter_with_labels_mems_used[local]:
  !n fn out lm. simplify_cfg_iter_with_labels n fn = (out,lm) ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[simplify_cfg_iter_with_labels_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  metis_tac[simplify_cfg_round_with_labels_mems_used]
QED

Theorem simplify_cfg_fn_with_labels_mems_used:
  simplify_cfg_fn_with_labels fn = (out,lm) ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[simplify_cfg_fn_with_labels_def] >>
  metis_tac[simplify_cfg_iter_with_labels_mems_used]
QED
